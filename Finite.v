Require Import Omega.

(* finite types used in defining memory as a finite map *)
Fixpoint fin (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => option (fin m)
  end.

(* Decidable equality for finite types *)
Definition fin_dec : forall {n} (f f' : fin n), ({f = f'} + {f <> f'}).
  intros n f f'.
  destruct n.
  - inversion f.
  -
    destruct f.
    destruct f'.
Admitted.

(* Get the mth element of the n-ary finite type *)
Fixpoint fin_n_m (n : nat) (m : {m : nat | m < n}) : fin n.
  destruct m.
  destruct n.
  - exfalso.
    inversion l.
  - destruct x.
    + exact None.
    +
      apply Some.
      apply fin_n_m.
      assert (x < n) by omega.
      exact (exist (fun m => m < n) x H).
Defined.
