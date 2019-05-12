Require Import Omega.
Require Import Finite.
From RecordUpdate Require Import RecordSet.
Require Import Types.
Require Import Registers.

Inductive bit : Type := zero | one.

Record flags : Type := mkFlags 
                         {
                           (* comparison flag set after doing a
                              comparison operation. Uses native Coq
                              comparison type so we can make use of
                              some lemmas maybe. *)
                           comparison : comparison
                           (* overflow bit that is set on or off
                              depending on the outcome of an
                              arithmetic instruction *)
                           ; overflow : bit
                         }.

Definition zeroFlags : flags := {| comparison := Eq;
                                   overflow := zero; |}.


(* In keeping with Knuth, we use a 4000-word memory *)
Definition size : nat := 4000.
Context (Hsizenontrivial : size > 0).

Definition address : Type := {n : nat | n < size}.

Module Type Memory.
  Context (memory : Type).
  Context (zeroMemory : memory).
  Context (HMemNontrivial : size > 0).
  Context (get_nth_cell : memory -> {n : nat | n < size} -> word5).
  Context (set_nth_cell : memory -> {n : nat | n < size} -> word5 -> memory).
  Notation " M [ n ] " := (get_nth_cell M n) (at level 50).
End Memory.

Module MixMemory : Memory.
  (* Each MIX machine has a 4000-word memory. We represent this in
     Coq as a finite map from a type with 4000 inhabitants to words. *)
  Definition memory := fin size -> word5.
  Let zero_word := of_Z5 0.
  Definition zeroMemory : memory := fun n => zero_word.
  Definition HMemNontrivial : size > 0.
    exact Hsizenontrivial.
  Defined.
  Definition mem_index (n : {n : nat | n < size}) : fin size := fin_n_m size n.
  Definition get_nth_cell M (n : {n : nat | n < size}) : word5 :=
    M (mem_index n).
  Definition set_nth_cell M (n : {n : nat | n < size}) (w : word5) : memory :=
    (fun m : fin size => if fin_dec m (mem_index n) then w else M m).
End MixMemory.

(* [TODO: move to Types.v about fieldspec] Knuth uses ':' but we depart from this and get similar aesthetics
   by squinting at Coq's pair syntax *)

Open Scope list_scope.

Import MixRegisters.

Definition sign := bool.

Inductive instruction : Type :=
(** * Loads and stores *)
(* Load a word (or part of it depending on the fieldspec), optionally
negating it using a negative sign, into a given register from a given
memory address possibly augmented by the value in a given index
register. *)
| Load : sign -> reg -> address -> option reg -> fieldspec -> instruction
| Store : reg -> address -> option fieldspec -> instruction
| StoreZero : address -> option fieldspec -> instruction
                                             
(** * Arithmetic *)                                            
| Add : address -> option fieldspec -> instruction
| Sub : address -> option fieldspec -> instruction
| Mul : address -> option fieldspec -> instruction
| Div : address -> option fieldspec -> instruction
                                       
(** * address transfer operations *)
(* Enter a word, optionally negating it and optionally adjusted by the value in a given index register, into a register *)
| Ent : sign -> reg -> Z -> option reg -> instruction
(* increase the value contained in a given register by a given word *)
| Inc : reg -> Z -> instruction
(* decrease the value contained in a given register by a given word *)
| Dec : reg -> Z -> instruction

(** * Comparison operators *)
| Cmp : reg -> address -> fieldspec -> instruction

(** * Jump operators *)
(* unconditional jump *)
| Jmp : address -> instruction
(* unconditional jump that doesn't update the jump register *)
| Jsj : address -> instruction
(* conditionally jump if there has been an overflow *)
| Jov : address -> instruction
(* conditionally jump if there hasn't been an overflow *)
| Jnov : address -> instruction
(* jump on less, equal, greater, greater-or-equal, unequal,
   less-or-equal comparison flags respectively *)
| Jl : address -> instruction
| Je : address -> instruction
| Jg : address -> instruction
| Jge : address -> instruction
| Jne : address -> instruction
| Jle : address -> instruction
(* jump on register negative, zero, positive, nonnegative, nonzero,
   nonpositive respectively *)
| Jrn : reg -> address -> instruction
| Jrz : reg -> address -> instruction
| Jrp : reg -> address -> instruction
| Jrnn : reg -> address -> instruction
| Jrnz : reg -> address -> instruction
| Jrnp : reg -> address -> instruction

(** * Miscellaneous operators *)
(** shifts *)
(* Shift a given register left or right by a given number of bytes *)
| Sl : reg -> nat -> instruction
| Sr : reg -> nat -> instruction
(* special AX-shifts *)
| Slax : nat -> instruction
| Srax : nat -> instruction
(* circular AX-shifts *)
| Slc : nat -> instruction
| Src : nat -> instruction

(* Move the number of words specified by the fieldspec from location M
   to the location specified by the contents of I1 *)
| Move : address -> fieldspec -> instruction

(* no-op *)
| Nop : instruction
(* halt the machine *)
| Hlt : instruction
          
(** * TODO: IO operators *)
(* Need to decide on how much I want to model this and how to do so *)
          
(** * TODO: Conversion operators *)
(* Left for later due to laziness *).
Import Registers.
Import MixMemory.

Record machine : Type := mkMachine {
                             r : registers;
                             f : flags;
                             m : memory
                           }.

Definition zeroMachine : machine := {| r := zeroRegisters;
                                       f := zeroFlags;
                                       m := zeroMemory |}.

Inductive indexRegister : reg -> Prop :=
  | indexI1 : indexRegister rI1
  | indexI2 : indexRegister rI2
  | indexI3 : indexRegister rI3
  | indexI4 : indexRegister rI4
  | indexI5 : indexRegister rI5
  | indexI6 : indexRegister rI6.

Inductive instWf : instruction -> Prop :=
| LoadWf : forall sign rDest from maybeIndex F,
    (forall Ind, maybeIndex = Some(Ind) -> indexRegister Ind) ->
    instWf (Load sign rDest from maybeIndex F)
| HaltWf : instWf Hlt.

(* For record updates *)
Instance etaMachine : Settable _ := settable! mkMachine <r; f; m>.
Import RecordSetNotations.

Close Scope Z_scope.
Open Scope nat_scope.

Definition address_with_offset (a : address) (o : nat) : address.
  unfold address.
  destruct a as [a' Ha'].
  refine (exist _ ((a' + o) mod size) _).
  (* N.mod_lt: forall a b : N, b <> 0%N -> (a mod b < b)%N *)
  Check Nat.mod_bound_pos.
  eapply Nat.mod_bound_pos; abstract omega.
Defined.

Definition instDenote (M : machine) (I : {I : instruction | instWf I}) : machine :=
  let (I, _) := I in 
  match I with
  | Load sign rDest from maybeIndex F =>
    let offsetFrom := (match maybeIndex with
                       | Some(Ind) =>
                         (* offset from by the value contained in I 
             N.b. by the behavior of Z.to_nat, we treat negative offsets from I as 0. *)
                         let o := Z.to_nat (getReg (r M) Ind) in
                         address_with_offset from o
                       | None => from
                       end)
    in let fromVal := fieldOf5 (get_nth_cell (m M) offsetFrom) (Zero, Five)
       in let newReg := setReg (r M) rDest fromVal in
    M <| r := newReg |>
 | _ => M
  end.

Definition Halto : {I : instruction | instWf I}.
  econstructor.
  instantiate (1 := Hlt).
  auto.
  constructor.
Defined.

Search memory.
Coercion of_Z5 : Z >-> word5.
Coercion of_Z2 : Z >-> word2.
Definition testMemory : memory.
  refine(set_nth_cell zeroMemory (exist _ 420 _) 69%Z).
  assert (size = 4000).
  auto.
  abstract omega.
Defined.

Definition testMachine : machine := zeroMachine <| m := testMemory |>.

Definition testInst : {I : instruction | instWf I}.
  refine (exist _ (Load true rA (exist _ 420 _) None (Zero, Five)) _).
  Unshelve. 2: { 
    assert (size = 4000). reflexivity. abstract omega.
  }

  eapply LoadWf.
  intros.
  inversion H.
Defined.

Print testInst.

Definition testMachineResult : machine := instDenote testMachine testInst.

Require Coq.extraction.Extraction.
Extraction Language OCaml.
Recursive Extraction testMachineResult.