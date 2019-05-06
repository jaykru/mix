Require Import Omega.
Require Import Finite.
From RecordUpdate Require Import RecordSet.
Require Import Types.
Require Import Registers.
Import MixShort MixWord.

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

Context (size : nat).
Context (Hsizenontrivial : size > 0).

Definition address : Type := {n : nat | n < size}.

Module Type Memory.
  Context (memory : Type).
  Context (zeroMemory : memory).
  Context (HMemNontrivial : size > 0).
  Context (get_nth_cell : memory -> {n : nat | n < size} -> word).
  Context (set_nth_cell : memory -> {n : nat | n < size} -> word -> memory).
  Notation " M [ n ] " := (get_nth_cell M n) (at level 50).
End Memory.

Module MixMemory : Memory.
  (* Each MIX machine has a 4000-word memory. We represent this in
     Coq as a finite map from a type with 4000 inhabitants to words. *)
  Definition memory := fin size -> word.
  Let zero_word := wordFromZ 0.
  Definition zeroMemory : memory := fun n => zero_word.
  Definition HMemNontrivial : size > 0.
    exact Hsizenontrivial.
  Defined.
  Definition mem_index (n : {n : nat | n < size}) : fin size := fin_n_m size n.
  Definition get_nth_cell M (n : {n : nat | n < size}) : word :=
    M (mem_index n).
  Definition set_nth_cell M (n : {n : nat | n < size}) (w : word) : memory :=
    (fun m : fin size => if fin_dec m (mem_index n) then w else M m).
End MixMemory.

(* Knuth uses ':' but we depart from this and get similar aesthetics
   by squinting at Coq's pair syntax *)
Definition fieldspec : Type := {L : nat | L < 6} * {R : nat | R < 6}.
Definition fieldspecToNat (F : fieldspec) : {n : nat | n < 64}.
  refine (exist _ (let (L', R') := F
                   in match L' with 
                      | exist _ L _ =>
                                    match R' with 
                                    | exist _ R _ => 8 * L + R
                                    end
                      end) _).
  unfold fieldspec in F.
  destruct F.
  destruct s, s0.
  omega.
Defined.

Open Scope list_scope.

Import MixRegisters.

Definition sign := bool.

Inductive instruction : Type :=
(** * Loads and stores *)
(* Load a word (or part of it depending on the fieldspec), optionally
negating it using a negative sign, into a given register from a given
memory address possibly augmented by the value in a given index
register. *)
| Load : sign -> reg -> address -> option reg -> option fieldspec -> instruction
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
| LoadWf : forall sign rDest from maybeIndex I maybeFieldspec,
    (maybeIndex = Some(I) -> indexRegister I) ->
    instWf (Load sign rDest from maybeIndex maybeFieldspec)
| HaltWf : instWf Hlt.

(* For record updates *)
Instance etaMachine : Settable _ := settable! mkMachine <r; f; m>.
Import RecordSetNotations.


Definition bits := list bit.
Definition bitsFromZ (z : Z) (width : nat) : option (sign * bits) :=
  let sign := match z with
              | Z0 => true
              | Zpos _ => true
              | Zneg _ => false
              end in
  let fix helper (left : Z) (w : nat) (acc : bits) :=
      match w with
      | 0 => 
      | S w' => 
  



Definition instDenote (M : machine) (I : {I : instruction | instWf I}) : machine :=
  let (I, _) := I in 
  match I with
  | Load sign rDest from maybeIndex maybeFieldspec =>
    match (maybeIndex, maybeFieldspec) with
    | (Some(I), Some(F)) =>
      (* offset from by the value contained in I *)
      let offset := indexToNat (getReg I) in
    | (Some(I), None) => 
    | (None, Some(F)) =>
    | (None, None) => 
      let fromVal := signedFromWord (get_nth_cell (m M) from)
      in let newReg := setReg (r M) rDest fromVal
         in M <| r := newReg |>
    end.


Compute (instDenote zeroMachine (exist _ Hlt _)).

    match (maybeIndex, maybeFieldspec) with
    | (Some(I), Some(F)) =>
      (* offset from by the value contained in I *)
      let offset := indexToNat (getReg I) in
    | (Some(I), None) => 
    | (None, Some(F)) =>
    | (None, None) => 
      let 
        {| r := 
             f := M.f;
           m := M.m;
        |}
      | otherwise => M
        end.

Definition Halto : {I : instruction | instWf I}.
  econstructor.
  instantiate (1 := Hlt).
  auto.
  constructor.
  Defined.

Compute instDenote zeroMachine Halto.

  in match I with
     | (Load sign rDest from maybeIndex maybeFieldspec, _) =>
       match (maybeIndex, maybeFieldspec) with
       | (Some(I), Some(F)) =>
         (* offset from by the value contained in I *)
         let offset := indexToNat (getReg I) in
       | (Some(I), None) => 
       | (None, Some(F)) =>
       | (None, None) => 
         let 
           {| r := 
                f := M.f;
              m := M.m;
           |}
         | otherwise => M
           end.
