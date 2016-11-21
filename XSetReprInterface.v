Require Import XSetInterface.
Require Classes.RelationClasses.

Module Type DecidableReprType (E : DecidableType) <: DecidableType.

Definition t := E.t.
Parameter eq : t -> t -> Prop.
Parameter eq_equiv : Equivalence eq.
Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.

Parameter repr : t -> t.
Parameter repr_mod : forall x : t, E.eq x (repr x).
Parameter repr_eq : forall x y : t, E.eq x y <-> eq (repr x) (repr y).
Parameter eq_sub : forall x y : t, eq x y -> E.eq x y.

End DecidableReprType.

(** Module for [Logic.eq] (some obvious specifications are omitted) *)
Module Type DecidableReprEq (E : DecidableType).

Definition t := E.t.
Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
Parameter repr : t -> t.
Parameter repr_mod : forall x : t, E.eq x (repr x).
Parameter repr_eq : forall x y : t, E.eq x y <-> repr x = repr y.

End DecidableReprEq.


(** DecidableReprEq -> DecidableReprType *)
Module DecidableReprEq2Type (E : DecidableType) (D : DecidableReprEq E) <: DecidableReprType E.

Definition t := E.t.
Definition eq := @Logic.eq t.
Definition eq_equiv := @RelationClasses.eq_equivalence t.
Definition eq_dec := D.eq_dec.

Definition repr := D.repr.
Lemma repr_mod : forall x : t, E.eq x (repr x).
exact D.repr_mod. Qed.
Lemma repr_eq : forall x y : t, E.eq x y <-> repr x = repr y.
exact D.repr_eq. Qed.
Lemma eq_sub : forall x y : t, x = y -> E.eq x y.
intros; subst.
now apply E.eq_equiv.
Qed.

End DecidableReprEq2Type.


Module DRTspec (E : DecidableType) (X : DecidableReprType E).

Import X.
Lemma repr_involution : forall x : t, eq (repr x) (repr (repr x)).
intro x; apply repr_eq; apply repr_mod.
Qed.

Lemma repr_eq' : forall x y : t, eq x y -> eq (repr x) (repr y).
intros x y Heq.
apply repr_eq.
apply eq_sub.
now auto.
Qed.

Lemma repr_exists : forall x : t, (exists y : t, eq (repr y) x) -> eq x (repr x).
intros.
destruct H as [y H].
apply eq_equiv with (repr y).
apply eq_equiv; now auto.
apply eq_equiv with (repr (repr y)).
now apply repr_involution.
apply repr_eq.
apply eq_sub.
now auto.
Qed.


End DRTspec.


Module Type WSetsRepr <: WSets.

Declare Module E : DecidableType.
Declare Module E' : DecidableReprType E.
Include WSetsOn E.

End WSetsRepr.



Module Type OrderedReprType (E : DecidableType) <: OrderedType.

Include DecidableReprType E.

Parameter lt : t -> t -> Prop.
Parameter lt_strorder : StrictOrder lt.
Parameter lt_compat : Proper (eq ==> eq ==> iff) lt.

Parameter compare : t -> t -> comparison.
Parameter compare_spec :
  forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).

End OrderedReprType.



Module OrderedRepr2Type (E : DecidableType) (E' : OrderedReprType E) <: OrderedType.

Include E.

Definition lt (x y : t) := E'.lt (E'.repr x) (E'.repr y).

Theorem lt_strorder : StrictOrder lt.
unfold lt; constructor.
 unfold Irreflexive.
  unfold complement, Reflexive.
   intro.
    now apply E'.lt_strorder.
 unfold Transitive.
  intros x y z.
   now apply E'.lt_strorder.
Qed.

Theorem lt_compat : Proper (eq ==> eq ==> iff) lt.
unfold Proper.
 compute.
  intros.
   apply E'.lt_compat; apply E'.repr_eq; now auto.
Qed.


Definition compare (x y : t) := E'.compare (E'.repr x) (E'.repr y).

Theorem compare_spec :
  forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
intros x y; unfold lt, compare.
 destruct (E'.compare_spec (E'.repr x) (E'.repr y)).
  apply CompEq; apply E'.repr_eq; now auto.
  apply CompLt; now auto.
  apply CompGt; now auto.
Qed.


End OrderedRepr2Type.


Module Type SetsRepr (T : DecidableType) (E' : OrderedReprType T) <: Sets.

Module E := OrderedRepr2Type T E'.
Include SetsOn E.

End SetsRepr.
