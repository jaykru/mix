(* Our formalization uses bits to reflect actual computing hardware,
but one could define a digits type in lieu of bits and redefine the
below bytes data-type to use that digits type and the rest of the
formalization (and critically all well-written MIX programs!) should
be fine. *)
Inductive bit : Type :=
| zero : bit
| one : bit.

(* Bytes are comprised of 6 bits. They can therefore hold values from
0 to 99, but we assume that bytes only hold 64 distinct values from
(i.e. values from 0 to 63) *)
Definition byte : Type := bit * bit * bit * bit * bit * bit.

Inductive sign : Type :=
| plus : sign
| minus : sign.

(* MIX words are comprised of a sign bit and 5 bytes *)
Definition word : Type := sign * byte * byte * byte * byte * byte.

Record registers : Type := mkRegisters 
                            {
                              (* Accumulator: "...has many uses,
                               especially for arithmetic and operating
                               on data." *)
                              A : word
                              (* Extension register: "...an extension
                              on the 'right-hand side' of rA, and it
                              is is used in conjuction with rA to hold
                              ten bytes of a product or dividend, or
                              it can be used to hold information
                              shifted to the right out of A." *)
                              ; X : word
                              (* Index registers comprised of a sign
                                 and two bytes: "...used primarily for
                                 for counting and for referencing
                                 variable memory addresses." *)
                              ; I1 : sign * byte * byte
                              ; I2 : sign * byte * byte
                              ; I3 : sign * byte * byte
                              ; I4 : sign * byte * byte
                              ; I5 : sign * byte * byte
                              ; I6 : sign * byte * byte
                              (* Jump register comprised of two bytes
                              and (TODO?) a sign, where the sign is
                              always considered positive: "...always
                              holds the address of the instruction
                              following the most recent 'jump'
                              operation, and it is primarily used in
                              connection with subroutines." *)
                              ; J : byte * byte
                            }.

Record flags : Type := mkFlags 
                         {
                           (* comparison flag set after doing a
                              comparison operation. Uses native Coq
                              comparison type so we can make use of
                              some lemmas maybe. *)
                           comparison : comparison
                           (* overflow bit that is set on or off
                           depending on the outcome of an arithmetic
                           instruction *)
                           ; overflow : bit
                         }.

(* finite types from autosubst2, used in defining memory as a finite map *)
Fixpoint fin (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => option (fin m)
  end.


Set Nested Proofs Allowed.
Definition fin_zero {n : nat} {H : n > 0} : fin (n).
  induction n.
  Lemma zgtz : 0 > 0 -> False.
    intro.
    inversion H.
  Qed.
  exact (zgtz H).

  inversion H.
  fold fin in *.
  destruct H.
  
  case n.
  inversion H.
  rewrite <-H0 in H.

  unfold ">" in H.
  

Fixpoint fin_m {n : nat} (m : nat) {H : m <= S n} {struct m} : fin (S n) :=
  


Compute (fin_m 400 : fin 4000).

(* Each MIX machine has a 4000-word of memory. We represent this in
Coq as a finite map from a type with 4000 inhabitants to words. *)
Definition memory : Type := fin 4000 -> word.

Notation " M [n] " := M (fin n).