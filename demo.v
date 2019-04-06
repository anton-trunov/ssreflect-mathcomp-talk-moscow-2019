Inductive le : nat -> nat -> Prop :=
| Le0 : forall n, le 0 n
| LeSS : forall {n m}, le n m -> le (S n) (S m).

Definition four_le_five : le 4 5 :=
  LeSS (LeSS (LeSS (LeSS (Le0 1)))).

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, _ => true
  | _, O => false
  | S n', S m' => leb n' m'
  end.

Coercion is_true b := b = true.

Definition four_le_five' : leb 4 5 := eq_refl.

(* ================================= *)


From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype.
Print Bool.reflect.

(* connection between le and leb *)
Lemma leP m n : reflect (le m n) (leb m n).
Proof. Admitted. (* see mathcomp/ssreflect/ssrnat.v *)

About andP.

Lemma foo b1 b2 : b1 && b2 -> b1. 
Proof.
(* to the world of logic and back *)
move/andP.
move/andP.
Abort.

Lemma foo' (T : eqType) (x y : T) : x == y -> y == x.
Proof.
move/eqP.
move=>->.
About eq_refl.
exact: eq_refl.  (* proof by reflexivity of == *)
Qed.


Module Trichotomy.

About ltngtP.

Example for_ltngtP m n :
  (m <= n) && (n <= m) -> (m == n) || (m > n) || (m + n == 0).
Proof.
by case: ltngtP.
Undo.
(* Set Printing Coercions. *)
case: ltngtP.
- move=> /=. done.
- move=> /=. done.
move=> /=. done.
(* Unset Printing Coercions. *)
Qed.

About eqP.
End Trichotomy.


(* ================================= *)


Module ProductEquality.

Print Canonical Projections.

Fail Compute (1, fun (x : nat) => 0) == (2, fun (x : nat) => 0).

Set Printing All.
Check (1, true) == (2, true).
Unset Printing All.

End ProductEquality.


(* ================================= *)


From mathcomp Require Import bigop.
Import Monoid.

(* keying on terms, as opposed to types *)
Lemma bar m n p q r :
  m + (n + p * (q * r)) = m + n + p * q * r.
Proof.
rewrite !mulmA /=.
done.
Qed.
