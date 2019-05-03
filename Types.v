Require Import Finite.
Require Import Omega.

Module Type Word.
  Context (size : {n : nat | n > 0}).
  Context (word : Type).
  Context (signed : word -> Z).
  Context (unsigned : word -> Z).
  Context (fromZ : Z -> word).
End Word.

Module MixWord : Word.
  Definition size : {n : nat | n > 0}. refine (exist _ 64 _); omega. Defined.
  Definition word : Type := Z.
  Open Scope Z_scope.
  Let wrap := let (w, _) := size in Z.of_nat w.
  (* Overflow doesn't change sign. Actually, Knuth is kind of vague
  about the semantics of overflow in TAOCP, I suppose leaving it as
  undefined behavior. *)
  Definition signed (w : word) : Z :=
    match w with
    | Z0 => w
    | Zpos x => w mod wrap
    | Zneg x => - ((Zpos x) mod wrap)
    end.

  Definition unsigned (w : word) : Z :=
    match w with
    | Z0 => w
    | Zpos x => w mod wrap
    | Zneg x => (Zpos x) mod wrap
    end.

  Definition fromZ (z : Z) : word := id z.
End MixWord.

Definition zero_word := MixWord.fromZ 0.
  
(* (* Our formalization uses bits to reflect actual computing hardware, *)
(*    but one could define a digits type in lieu of bits and redefine the *)
(*    below bytes data-type to use that digits type and the rest of the *)
(*    formalization (and critically all well-written MIX programs!) *)
(*    should be fine. *) *)
(*   Inductive bit : Type := *)
(*   | one : bit *)
(*   | zero : bit. *)

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