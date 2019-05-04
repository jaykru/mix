Require Import Finite.
Require Import Omega.

Module Type Word.
  Context (width : {n : nat | n > 0}).
  Context (word : Type).
  Context (signedFromWord : word -> Z).
  Context (unsignedFromWord : word -> Z).
  Context (wordFromZ : Z -> word).
End Word.

Module Type Short.
  Context (width : {n : nat | n > 0}).
  Context (short : Type).
  Context (signedFromShort : short -> Z).
  Context (unsignedFromShort : short -> Z).
  Context (shortFromZ : Z -> short).
End Short.

Module MixShort : Short.
  (* 6 bits per byte * 2 bytes / short = 12 bits / short *)
  Definition width : {n : nat | n > 0}. refine (exist _ 12 _); omega. Defined.
  Definition short : Type := Z.
  Open Scope Z_scope.
  Let width' := let (w, _) := width in Z.of_nat w.
  Let wrap := 2 ^ width'.
  
  (* Overflow doesn't change sign. Actually, Knuth is kind of vague
  about the semantics of overflow in TAOCP, I suppose leaving it as
  undefined behavior. *)
  Definition signedFromShort (s : short) : Z :=
    match s with
    | Z0 => s
    | Zpos x => s mod wrap
    | Zneg x => - ((Zpos x) mod wrap)
    end.

  Definition unsignedFromShort (s : short) : Z :=
    match s with
    | Z0 => s
    | Zpos x => s mod wrap
    | Zneg x => (Zpos x) mod wrap
    end.

  Definition shortFromZ (z : Z) : short := id z.
End MixShort.

Module MixWord : Word.
  (* 6 bits per byte * 5 bytes / word = 30 bits / word *)
  Definition width : {n : nat | n > 0}. refine (exist _ 30 _); omega. Defined.
  Definition word : Type := Z.
  Open Scope Z_scope.
  Let width' := let (w, _) := width in Z.of_nat w.
  Let wrap := 2 ^ width'.
  (* Overflow doesn't change sign. Actually, Knuth is kind of vague
  about the semantics of overflow in TAOCP, I suppose leaving it as
  undefined behavior. *)
  Definition signedFromWord (w : word) : Z :=
    match w with
    | Z0 => w
    | Zpos x => w mod wrap
    | Zneg x => - ((Zpos x) mod wrap)
    end.

  Definition unsignedFromWord (w : word) : Z :=
    match w with
    | Z0 => w
    | Zpos x => w mod wrap
    | Zneg x => (Zpos x) mod wrap
    end.

  Definition wordFromZ (z : Z) : word := id z.
End MixWord.

Import MixWord.
Import MixShort.

Definition shortToWord s := wordFromZ (signedFromShort s).
Global Coercion shortToWord : short >-> word.

(* Our formalization uses bits to reflect actual computing hardware, *)
(*    but one could define a digits type in lieu of bits and redefine the *)
(*    below bytes data-type to use that digits type and the rest of the *)
(*    formalization (and critically all well-written MIX programs!) *)
(*    should be fine. *)
  Inductive bit : Type :=
  | one : bit
  | zero : bit.

(* (* Bytes are comprised of 6 bits. They can therefore hold values from *)
(*    0 to 99, but we assume that bytes only hold 64 distinct values from *)
(*    (i.e. values from 0 to 63) *) *)
(*   Definition byte : Type := bit * bit * bit * bit * bit * bit. *)

(*   Definition byteToNat (B : byte) : nat := *)
(*     match B with *)
(*     | (b5,b4,b3,b2,b1,b0) => *)
(*       (if b5 then 2 ^ 5 else 0) + *)
(*       (if b4 then 2 ^ 4 else 0) + *)
(*       (if b3 then 2 ^ 3 else 0) + *)
(*       (if b2 then 2 ^ 2 else 0) + *)
(*       (if b1 then 2 ^ 1 else 0) + *)
(*       (if b0 then 2 ^ 0 else 0) *)
(*     end. *)

(* Require Import Coq.Program.Wf. *)
(* Program Fixpoint natToBits (n : nat) {wf lt n} : list bit := *)
(*   match n with *)
(*   | 0 => nil *)
(*   | S n' => List.rev ((if (Nat.eq_dec (n mod 2) 0) then zero else one) :: natToBits (Nat.div2 n)) *)
(*   end. *)
(* Obligation 1. *)
(* apply Nat.lt_div2. *)
(* omega. *)
(* Qed. *)

(* Import List.ListNotations. *)
(* Open Scope list_scope. *)
(* Compute natToBits 11. *)

(* Search "Z". *)

(* (* MIX words are comprised of a sign bit and 5 bytes *) *)
(* Definition word : Type := sign * byte * byte * byte * byte * byte. *)

(* Definition nat_to_byte (n : {n : nat | n < 64}) : byte := fin_n_m 64 n. *)
(* Definition byte_to_nat (b : byte) : {n : nat | n < 64} *)

(* Definition zero_byte : byte. *)
(*   apply n_byte. *)
(*   econstructor. *)
(*   instantiate (1 := 0). *)
(*   abstract omega. *)
(* Defined. *)
       
(* (* Definition zero_byte : byte := (zero , zero , zero , zero , zero , zero). *) *)
(* Definition zero_word : word := (plus , zero_byte , zero_byte , zero_byte , zero_byte , zero_byte). *)