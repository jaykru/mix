From RecordUpdate Require Import RecordSet.
Require Import Types.
Import MixShort MixWord. (* TODO: why doesn't Import Types.MixWord work? *)
Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Local Open Scope Z_scope.

Inductive reg : Type :=
    (* general purpose *)
    rA | rX
    (* index registers *)
    | rI1 | rI2 | rI3 | rI4 | rI5 | rI6
    (* jump register *)
    | rJ.

Module Type Registers.
  Context (registers : Type).
  Context (short : Type).
  Context (word : Type).
  Context (zeroRegisters : registers).

  Context (getReg : registers -> reg -> Z).
  Context (setReg : registers -> reg -> Z -> registers).
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
                                 ; I1 : short
                                 ; I2 : short
                                 ; I3 : short
                                 ; I4 : short
                                 ; I5 : short
                                 ; I6 : short
                                 (* Jump register comprised of two bytes
                                    and (TODO?) a sign, where the sign is
                                    always considered positive: "...always
                                    holds the address of the instruction
                                    following the most recent 'jump'
                                    operation, and it is primarily used in
                                    connection with subroutines." *)
                                 ; J : short
                               }.
  Definition registers : Type := registers'.

  Definition short : Type := short.
  Definition word : Type := word.

  (* For record updates *)
  Instance etaRegisters : Settable _ := settable! mkRegisters <A; X; I1; I2; I3; I4; I5; I6; J>.

  Let zero_short := shortFromZ 0.
  Let zero_word := shortFromZ 0.

  Definition zeroRegisters : registers := {| A := zero_word;
                                             X := zero_word;
                                             I1 := zero_short;
                                             I2 := zero_short;
                                             I3 := zero_short;
                                             I4 := zero_short;
                                             I5 := zero_short;
                                             I6 := zero_short;
                                             J := zero_short; |}.

Print Registers.

Print Word.
Definition getReg (R : registers) (r : reg) : Z :=
  match r with
  | rA => signedFromWord (A R)
  | rX => signedFromWord (X R)
  | rI1 => signedFromShort (I1 R)
  | rI2 => signedFromShort (I2 R)
  | rI3 => signedFromShort (I3 R)
  | rI4 => signedFromShort (I4 R)
  | rI5 => signedFromShort (I5 R)
  | rI6 => signedFromShort (I6 R)
  | rJ => unsignedFromShort (J R) (* per Knuth, the jump register does have a sign, but we always ignore it *)
  end.
    
  Import RecordSetNotations.
  Definition setReg (R : registers) (r : reg) (z : Z) : registers :=
    let w := wordFromZ z in
    let s := shortFromZ z in 
    match r with
    | rA => R <|A := w|>
    | rX => R <|X := w|>
    | rI1 => R <|I1 := s|>
    | rI2 => R <|I2 := s|>
    | rI3 => R <|I3 := s|>
    | rI4 => R <|I4 := s|>
    | rI5 => R <|I5 := s|>
    | rI6 => R <|I6 := s|>
    | rJ => R <|J := s|>
    end.
End MixRegisters.