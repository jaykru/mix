From RecordUpdate Require Import RecordSet.

Module Type Registers.
  Context (registers : Type).
  Context (zeroRegisters : registers).
  Context (getReg : registers -> reg -> word + sign * byte * byte + byte * byte).
  Context (setReg : registers -> reg -> word + sign * byte * byte + byte * byte -> registers).
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