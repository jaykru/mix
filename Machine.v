Require Import Omega.
From RecordUpdate Require Import RecordSet.
Require Import Types.
Require Import Registers.

Open Scope list_scope.

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
                           (* Departure from Knuth: we add a flag for error conditions and halting *)
                           ; halt : bit
                         }.

Definition zeroFlags : flags := {|
                                 comparison := Eq
                                 ; overflow := zero
                                 ; halt := zero
                               |}.


(* In keeping with Knuth, we use a 4000-word memory *)
Definition size : nat := 4000.

Module MixMemory.
  (* Each MIX machine has a 4000-word memory. We represent this in Coq
  as a morally-partial map (using an option type as our codomain) from
  nat to words. *)
  Definition memory := nat -> option word5.
  Let zero_word := of_Z5 0.
  Definition zeroMemory : memory := fun n => if Nat.ltb n size then Some(zero_word) else None.
  Definition get_nth_cell (M : memory) n : option word5 := M n.
  Definition set_nth_cell M (n : nat) (w : word5) : option memory :=
    if Nat.ltb n size then Some(fun m : nat => if Nat.eqb m n then Some(w) else M m) else None.
End MixMemory.

Import MixRegisters.

Definition address := nat.

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
| HaltWf : instWf Hlt
| NopWf : instWf Nop.

(* For record updates *)
Instance etaMachine : Settable _ := settable! mkMachine <r; f; m>.
Import RecordSetNotations.

Close Scope Z_scope.
Open Scope nat_scope.

Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monad.
Import MonadNotation.
Open Scope monad_scope.
Print ExtLib.Structures.Monad.

Definition runInst (M : machine) (I : {I : instruction | instWf I}) : option machine :=
  let (I, _) := I in 
  match I with
  | Load sign rDest from maybeIndex F =>
    let offsetFrom := (match maybeIndex with
                       | Some(Ind) =>
                         (* offset from by the value contained in I 
             N.b. by the behavior of Z.to_nat, we treat negative offsets from I as 0. *)
                         let o := Z.to_nat (getReg (r M) Ind) in
                         (from + o) mod size
                       | None => from
                       end)
    in fromWord <- (get_nth_cell (m M) offsetFrom);;
       let fromVal := fieldOf5 fromWord (Zero, Five)
             in let newReg := setReg (r M) rDest fromVal in
                Some(M <| r := newReg |>)

  | Nop => Some(M)
  | _ => Some(M)
  end.

Definition Halto : {I : instruction | instWf I}.
  econstructor.
  instantiate (1 := Hlt).
  auto.
  constructor.
Defined.

Coercion of_Z5 : Z >-> word5.
Coercion of_Z2 : Z >-> word2.
Definition testMemory : memory.
  (pose (set_nth_cell zeroMemory 420 69%Z)).
  compute in *.
  exact (fun m : nat =>
          if
           (fix eqb (n m0 : nat) {struct n} : bool :=
              match n with
              | 0 => match m0 with
                     | 0 => true
                     | S _ => false
                     end
              | S n' => match m0 with
                        | 0 => false
                        | S m' => eqb n' m'
                        end
              end) m 420
          then Some 69%Z
          else
           if
            (fix leb (n m0 : nat) {struct n} : bool := match n with
                                                       | 0 => true
                                                       | S n' => match m0 with
                                                                 | 0 => false
                                                                 | S m' => leb n' m'
                                                                 end
                                                       end) m 3999
           then Some 0%Z
           else None).
Defined.

Definition testMachine : machine := zeroMachine <| m := testMemory |>.

Definition testInst : {I : instruction | instWf I}.
  refine (exist _ (Load plus rA 420 None (Zero, Five)) _).
  eapply LoadWf.
  intuition.
  inversion H.
Defined.

Print testInst.

Goal (forall M, (runInst testMachine testInst = Some(M)) 
           ->
           (A (r M)) = 69%Z).
  intuition.
  compute in *.
  inversion H.
  trivial.
Defined.

Inductive program : Type :=
| Seq : {I : instruction | instWf I} -> program -> program
| Done : program.

Fixpoint runProgram (M : machine) (P : program) : option machine :=
  match P with
  | Seq i P' => 
    M' <- runInst M i;;
    Mstar <- runProgram M' P';;
    ret Mstar
  | Done => 
    ret M
  end.

Definition triple (P : machine -> Prop) (C : program) (Q : machine -> Prop) :=
  forall (Start : machine), P Start -> forall M', Some(M') = runProgram Start C -> Q M'.

Definition myPreCondition (M : machine) : Prop := get_nth_cell (m M) 420 = Some(69%Z).
Definition myPostCondition (M : machine) : Prop := A (r M) = 69%Z.
Definition myProgram := Seq testInst Done.

(* want something like this but it doesn't do quite what I want. *)
Ltac unfurlProgram P :=
  match P with
  | Seq ?i ?P' => try unfold i; unfurlProgram P'
  | Done => idtac P
  end.

Ltac byCompute :=
  match goal with
  | [  |- triple ?P ?C ?Q] => unfold P; unfold C; unfold Q; unfold triple; unfold runProgram; unfold runInst; intuition
  end.

Goal triple myPreCondition myProgram myPostCondition.
  byCompute.
  unfold testInst in *.
  rewrite H in *.
  simpl in *.
  inversion H0; subst.
  auto.
Defined.

Notation "{{ P }} C {{ Q }}" :=  (triple P C Q) (at level 50).

Definition prettyPrintMemory (M : memory) : option (list word5) :=
  let fix do (s : nat) :=
      match s with
      | S s' => v <- (M s);;
               vs <- do s';;
               ret (v :: vs) 
      | 0 => Some(nil)
      end
  in do (size - 1).

Definition doNothing: program.
  refine (Seq (exist _ Nop _) Done); econstructor.
Defined.


(* Axiom of Hoare logic, but we can prove it *)
Theorem empty_statement: forall P,
    {{P}} doNothing {{P}}.
  intro.
  unfold doNothing.
  unfold triple.
  intros.
  simpl in *.
  injection H0.
  intro.
  subst.
  auto.
Defined.

Fixpoint comp (S T: program): program :=
  match S with
  | Done => Done
  | Seq s' s'' => Seq s' (comp s'' T)
  end.

Notation " S ;; T " := (comp S T).

Axiom seqComp: forall P Q R (S T: program),
    {{P}} S {{Q}} ->
    {{Q}} T {{R}} ->
    {{P}} S ;; T {{R}}.

        
Require Coq.extraction.Extraction.
Extraction Language OCaml.
