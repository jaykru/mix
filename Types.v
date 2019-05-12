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

Ltac easy_subset n :=
  refine (exist _ n _); try omega; auto.

Definition _word : {n : nat | n > 0} -> {n : nat | n > 0} -> Type := fun _ _ => Z.

Section withWidth.
  (* Parameterize operations on words over number of bits per byte and number of bytes per word. We will stay faithful to Knuth with 6-bit bytes and 5-byte words. *)
  Context (byteWidth : {n : nat | n > 0}).
  Context (wordWidth : {n : nat | n > 0}).
  Let byteWrap := let (bw, _) := byteWidth in
                  (2 ^ (Z.of_nat bw))%Z.
  Let wordWrap := let (bw,_) := byteWidth in
              let (ww,_) := wordWidth in
              let (b,w) := (Z.of_nat bw, Z.of_nat ww) in
              (2 ^ (b*w))%Z.

  Open Scope Z_scope.
  Definition word : Type := _word byteWidth wordWidth.
  (* Overflow doesn't change sign. Actually, Knuth is kind of vague
  about the semantics of overflow in TAOCP, I suppose leaving it as
  undefined behavior. *)
  Let signed (w : word) : Z :=
    match w with
    | Z0 => w
    | Zpos x => w mod wordWrap
    | Zneg x => - ((Zpos x) mod wordWrap)
    end.

  Let unsigned (w : word) : Z :=
    match w with
    | Z0 => w
    | Zpos x => w mod wordWrap
    | Zneg x => (Zpos x) mod wordWrap
    end.

  Let signOf (w : word) : sign :=
    match w with
      | Zneg _ => minus
      | _ => plus
    end.

  Definition of_Z (z : Z) : word := signed z.

  Let nthByte (w : word) (n : nat) : Z :=
    let w' := unsigned w in
    let fix do (left : word) (m : nat) :=
        match m with
        | O => left mod byteWrap
        | S m' => do (left / byteWrap) m'
        end
    in do w' n.

  Let bytesOf (w : word) : list Z :=
    let w' := unsigned w in
    let fix do (w : word) (n : nat) (acc : list Z) :=
        match n with
        | O => w mod byteWrap :: acc
        | S n' => do (w / byteWrap) n' (w mod byteWrap :: acc)
        end
    in do w' 4%nat [].

  Let of_bytes (bs : list Z) : word :=
    let fix do (bs : list Z) (acc : Z) (n : Z) :=
        match bs with
        | b :: bs => do bs (acc + (b * (byteWrap ^ n))) (n - 1)
        | [] => acc
        end
    in let n := Z.of_nat(length bs) in
       do bs 0 (n-1).

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
    do l (L-1)%nat R [].
  
  Definition fieldOf (w : word) (F : fieldspec) : word :=
    let (L, R) := F in
    match (R ?= L)%nat with
    | Gt =>
      let (s,v) := (match L with
                    (* the field includes the sign bit *)
                    | Zero => (signOf w, unsigned w)
                    (* the field includes'nt the sign bit *)
                    | otherwise => (plus, unsigned w)
                    end) in
      (* Grab bytes L through R from the word w and treats them as a
         word of their own with sign s, where the rightmost byte of the
         selection occupying the rightmost position in the resulting
         word *)
      let bs := bytesOf w in
      let fieldSlice := slice bs L (R + 1) in
      let newWord := (unsigned (of_bytes fieldSlice)) in 
      match s with
      | plus => newWord
      | minus => (- newWord)%Z
      end
    | otherwise => 0%Z (* when requesting a field of width 0 or less, just return the trivial word. *)
    end.
End withWidth.

Definition _6 : {n : nat | n > 0}. easy_subset 6. Defined.
Definition _5 : {n : nat | n > 0}. easy_subset 5. Defined.
Definition _2 : {n : nat | n > 0}. easy_subset 2. Defined.
Notation word5 := (word _6 _5).
Notation word2 := (word _6 _2).

Definition of_Z5 : Z -> word5 := of_Z _6 _5.
Definition of_Z2 : Z -> word2 := of_Z _6 _2.

Definition fieldOf5 : word5 -> fieldspec -> Z := fieldOf _6 _5.
Definition fieldOf2 : word2 -> fieldspec -> Z := fieldOf _6 _2.