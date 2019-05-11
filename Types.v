Require Import Finite.
Require Import Omega.
Require Import List.
Import ListNotations.

Inductive field : Type := Zero | One | Two | Three | Four | Five.
Definition fieldspec : Type := field * field.

Notation " 0 " := Zero : fieldspec_scope.
Notation " 1 " := One : fieldspec_scope.
Notation " 2 " := Two : fieldspec_scope.
Notation " 3 " := Three : fieldspec_scope.
Notation " 4 " := Four : fieldspec_scope.
Notation " 5 " := Five : fieldspec_scope.

Definition fieldToNat (f : field) : nat :=
  match f with
  | Zero => 0
  | One => 1
  | Two => 2
  | Three => 3
  | Four => 4
  | Five => 5
  end.

Coercion fieldToNat : field >-> nat.
Import Nat.
Compute (compare Zero One).


Delimit Scope fieldspec_scope with fieldspec.

Inductive sign : Type := plus | minus.

Module Type Word.
  (* Number of bits per byte *)
  Context (byteWidth : {n : nat | n > 0}).
  
  (* Number of bytes per word *)
  Context (wordWidth : {n : nat | n > 0}).
  
  Context (word : Type).
  Context (signedFromWord : word -> Z).
  Context (unsignedFromWord : word -> Z).
  Context (fieldFromWord : word -> fieldspec -> Z).
  Context (wordFromZ : Z -> word).
End Word.

Ltac easy_subset n :=
  refine (exist _ n _); try omega; auto.

Module MixWord : Word.
  (* We stay faithful to Knuth with 6-bit bytes and 5-byte words. *)
  Definition byteWidth : {n : nat | n > 0}. easy_subset 6. Defined.
  Definition wordWidth : {n : nat | n > 0}. easy_subset 5. Defined.
  Let byteWrap := let (bw, _) := byteWidth in
                  (2 ^ (Z.of_nat bw))%Z.
  Let wordWrap := let (bw,_) := byteWidth in
              let (ww,_) := wordWidth in
              let (b,w) := (Z.of_nat bw, Z.of_nat ww) in
              (2 ^ (b*w))%Z.

  Definition word : Type := Z.
  (* Overflow doesn't change sign. Actually, Knuth is kind of vague
  about the semantics of overflow in TAOCP, I suppose leaving it as
  undefined behavior. *)
  Definition signedFromWord (w : word) : Z :=
    match w with
    | Z0 => w
    | Zpos x => (w mod wordWrap)%Z
    | Zneg x => (- ((Zpos x) mod wordWrap))%Z
    end.

  Definition unsignedFromWord (w : word) : Z :=
    match w with
    | Z0 => w
    | Zpos x => (w mod wordWrap)%Z
    | Zneg x => ((Zpos x) mod wordWrap)%Z
    end.

  Let signOf (w : word) : sign :=
    match w with
      | Zneg _ => minus
      | _ => plus
    end.

  Definition wordFromZ (z : Z) : word := z.

  Let nthByte (w : word) (n : nat) : Z :=
    let w' := unsignedFromWord w in
    let fix do (left : word) (m : nat) :=
        match m with
        | O => (left mod byteWrap)%Z
        | S m' => do (left / byteWrap)%Z m'
        end
    in do w' n.

  Let bytesOf (w : word) : list Z :=
    let w' := unsignedFromWord w in
    let fix do (w : word) (n : nat) (acc : list Z) :=
        match n with
        | O => (w mod byteWrap)%Z :: acc
        | S n' => do (w / byteWrap)%Z n' ((w mod byteWrap)%Z :: acc)
        end
    in do w' 5 [].

  Let bytesToWord (bs : list Z) : word :=
    let fix do (bs : list Z) (acc : Z) (n : Z) :=
        match bs with
        | b :: bs => do bs (acc + (b * (byteWrap ^ n)))%Z (n - 1)%Z
        | [] => acc
        end
    in let n := Z.of_nat(length bs) in
       do bs 0%Z (n-1)%Z.

  Let slice {A} (l : list A) (L R : nat) : list A :=
    (* slice the list l, yielding a list containing the elements l[i] for i \in [L-1, R) *)
    let fix do (l : list A) (L R : nat) (acc : list A) :=
        match l with
        | l :: ls => 
          match L with
          | O =>
            match R with
            | O => List.rev acc
            | S R' => do ls L R' (l :: acc)
            end
          | S L' => do ls L' R acc
          end
        | [] => List.rev acc
        end
    in
    do l (L-1) R [].
  
  Definition fieldFromWord (w : word) (F : fieldspec) : word :=
    let (L, R) := F in
    match (R ?= L) with
    | Gt =>
      let (s,v) := (match L with
                    (* the field includes the sign bit *)
                    | Zero => (signOf w, unsignedFromWord w)
                    (* the field includes'nt the sign bit *)
                    | otherwise => (plus, unsignedFromWord w)
                    end) in
      (* Grab bytes L through R from the word w and treats them as a
         word of their own with sign s, where the rightmost byte of the
         selection occupying the rightmost position in the resulting
         word *)
      let bs := bytesOf w in
      let fieldSlice := slice bs L (R + 1) in
      let newWord := (unsignedFromWord (bytesToWord fieldSlice)) in 
      match s with
      | plus => newWord
      | minus => (- newWord)%Z
      end
    | otherwise => 0%Z (* when requesting a field of width 0 or less, just return the trivial word. *)
    end.
End MixWord.

Compute MixWord.unsignedFromWord (MixWord.wordFromZ  50%Z).

Module Type Short.
  (* Number of bits per byte *)
  Context (byteWidth : {n : nat | n > 0}).
  
  (* Number of bytes per short *)
  Context (shortWidth : {n : nat | n > 0}).
  
  Context (short : Type).
  Context (signedFromShort : short -> Z).
  Context (unsignedFromShort : short -> Z).
  Context (fieldFromShort : short -> fieldspec -> Z).
  Context (shortFromZ : Z -> short).
End Short.

Delimit Scope fieldspec_scope with F.
Import MixWord.
Goal 50%Z = (MixWord.fieldFromWord (MixWord.wordFromZ 50) (0%F ,5%F)).


Module MixShort : Short.
  (* We stay faithful to Knuth with 6-bit bytes and 5-byte words. *)
  Definition byteWidth : {n : nat | n > 0}. easy_subset 6. Defined.
  Definition shortWidth : {n : nat | n > 0}. easy_subset 2. Defined.
  Let byteWrap := let (bw, _) := byteWidth in
                  (2 ^ (Z.of_nat bw))%Z.
  Let shortWrap := let (bw,_) := byteWidth in
              let (ww,_) := shortWidth in
              let (b,w) := (Z.of_nat bw, Z.of_nat ww) in
              (2 ^ (b*w))%Z.

  Definition short : Type := Z.
  (* Overflow doesn't change sign. Actually, Knuth is kind of vague
  about the semantics of overflow in TAOCP, I suppose leaving it as
  undefined behavior. *)
  Definition signedFromShort (s : short) : Z :=
    match s with
    | Z0 => s
    | Zpos x => (s mod shortWrap)%Z
    | Zneg x => (- ((Zpos x) mod shortWrap))%Z
    end.

  Definition unsignedFromWord (w : word) : Z :=
    match w with
    | Z0 => w
    | Zpos x => (w mod wordWrap)%Z
    | Zneg x => ((Zpos x) mod wordWrap)%Z
    end.

  Let signOf (w : word) : sign :=
    match w with
      | Zneg _ => minus
      | _ => plus
    end.

  Definition wordFromZ (z : Z) : word := z.

  Let nthByte (w : word) (n : nat) : Z :=
    let w' := unsignedFromWord w in
    let fix do (left : word) (m : nat) :=
        match m with
        | O => (left mod byteWrap)%Z
        | S m' => do (left / byteWrap)%Z m'
        end
    in do w' n.

  Let bytesOf (w : word) : list Z :=
    let w' := unsignedFromWord w in
    let fix do (w : word) (n : nat) (acc : list Z) :=
        match n with
        | O => (w mod byteWrap)%Z :: acc
        | S n' => do (w / byteWrap)%Z n' ((w mod byteWrap)%Z :: acc)
        end
    in do w' 5 [].

  Let bytesToWord (bs : list Z) : word :=
    let fix do (bs : list Z) (acc : Z) (n : Z) :=
        match bs with
        | b :: bs => do bs (acc + (b * (byteWrap ^ n)))%Z (n - 1)%Z
        | [] => acc
        end
    in let n := Z.of_nat(length bs) in
       do bs 0%Z (n-1)%Z.

  Let slice {A} (l : list A) (L R : nat) : list A :=
    (* slice the list l, yielding a list containing the elements l[i] for i \in [L-1, R) *)
    let fix do (l : list A) (L R : nat) (acc : list A) :=
        match l with
        | l :: ls => 
          match L with
          | O =>
            match R with
            | O => List.rev acc
            | S R' => do ls L R' (l :: acc)
            end
          | S L' => do ls L' R acc
          end
        | [] => List.rev acc
        end
    in
    do l (L-1) R [].
  
  Definition fieldFromWord (w : word) (F : fieldspec) : word :=
    let (L, R) := F in
    match (R ?= L) with
    | Gt =>
      let (s,v) := (match L with
                    (* the field includes the sign bit *)
                    | Zero => (signOf w, unsignedFromWord w)
                    (* the field includes'nt the sign bit *)
                    | otherwise => (plus, unsignedFromWord w)
                    end) in
      (* Grab bytes L through R from the word w and treats them as a
         word of their own with sign s, where the rightmost byte of the
         selection occupying the rightmost position in the resulting
         word *)
      let bs := bytesOf w in
      let fieldSlice := slice bs L (R + 1) in
      let newWord := (unsignedFromWord (bytesToWord fieldSlice)) in 
      match s with
      | plus => newWord
      | minus => (- newWord)%Z
      end
    | otherwise => 0%Z (* when requesting a field of width 0 or less, just return the trivial word. *)
    end.
