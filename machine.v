Require Import Omega.
Require Import Finite.
From RecordUpdate Require Import RecordSet.
Require Import Types.
Import MixWord.

Inductive reg : Type :=
    (* general purpose *)
    rA | rX
    (* index registers *)
    | rI1 | rI2 | rI3 | rI4 | rI5 | rI6
    (* jump register *)
    | rJ.

Module Type Registers.
  Context (registers : Type).
  Context (zeroRegisters : registers).
  Context (getReg : registers -> reg -> word).
  Context (setReg : registers -> reg -> word -> registers).
End Registers.

Module MixRegisters : Registers.
  (* Dumb coq bug: the kernel won't let you instantiate a parameter
     with an record type (nor with an inductive definition)
     directly. *)
  Record registers' : Type := mkRegisters 
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
  Definition registers : Type := registers'.

  (* For record updates *)
  Instance etaRegisters : Settable _ := settable! mkRegisters <A; X; I1; I2; I3; I4; I5; I6; J>.

  Definition zeroRegisters : registers := {| A := zero_word;
                                             X := zero_word;
                                             I1 := (plus , zero_byte , zero_byte);
                                             I2 := (plus , zero_byte , zero_byte);
                                             I3 := (plus , zero_byte , zero_byte);
                                             I4 := (plus , zero_byte , zero_byte);
                                             I5 := (plus , zero_byte , zero_byte);
                                             I6 := (plus , zero_byte , zero_byte);
                                             J := (zero_byte , zero_byte); |}.
  

  
  Definition getReg (R : registers) (r : reg) : word + (sign * byte * byte) + (byte * byte) :=
    match r with
    | rA => inl (inl (A R))
    | rX => inl (inl (X R))
    | rI1 => inl (inr (I1 R))
    | rI2 => inl (inr (I2 R))
    | rI3 => inl (inr (I3 R))
    | rI4 => inl (inr (I4 R))
    | rI5 => inl (inr (I5 R))
    | rI6 => inl (inr (I6 R))
    | rJ => inr (J R)
    end.
  
  Import RecordSetNotations.
  Definition setReg (R : registers) (r : reg) (w : word + (sign * byte * byte) + (byte * byte) ) : registers :=
    match w with
    | inl (inl w) =>
      match r with
      | rA => R <|A := w|>
      | rX => R <|X := w|>
      | otherwise => R
      end
    | inl (inr s) =>
      match r with
        | rI1 => R <|I1 := s|>
        | rI2 => R <|I2 := s|>
        | rI3 => R <|I3 := s|>
        | rI4 => R <|I4 := s|>
        | rI5 => R <|I5 := s|>
        | rI6 => R <|I6 := s|>
        | _ => R
      end
    | inr s =>
      match r with
      | rJ => R <|J := s|>
      | _ => R
      end
    end.
End MixRegisters.

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

Definition address : Type := fin size.

Module Type Memory.
  Context {size : nat}.
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
  Definition size := size.
  Definition memory := fin size -> word.
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

Definition fieldspecToByte F := natToByte (fieldspecToNat F).

Import MixRegisters.

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
                                       
(** * Address transfer operations *)
(* Enter a word, optionally negating it and optionally adjusted by the value in a given index register, into a register *)
| Ent : sign -> reg -> word -> option reg -> instruction
(* increase the value contained in a given register by a given word *)
| Inc : reg -> word -> instruction
(* decrease the value contained in a given register by a given word *)
| Dec : reg -> word -> instruction

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
| Sl : reg -> word -> instruction
| Sr : reg -> word -> instruction
(* special AX-shifts *)
| Slax : word -> instruction
| Srax : word -> instruction
(* circular AX-shifts *)
| Slc : word -> instruction
| Src : word -> instruction

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

Definition instDenote (M : machine) (I : {I : instruction | instWf I}) : machine :=
  let (I, _) := I in 
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
