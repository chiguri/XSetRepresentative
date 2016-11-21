Require Import XSetInterface.
Require Import XSetReprInterface.

Module WRawSetReprWrapper (X : DecidableType) (X' : DecidableReprType X) (F : WSetsOn) <: WRawSets X.


Module WS := F X'.
Module Xspec := DRTspec X X'.

Definition elt := X.t.
Definition t := WS.t.

Notation "# x" := (X'.repr x) (at level 30, right associativity).

Definition empty := WS.empty.
Definition is_empty := WS.is_empty.
Definition mem (x : elt) (s : t) := WS.mem (#x) s.
Definition add (x : elt) (s : t) := WS.add (#x) s.
Definition singleton (x : elt) := WS.singleton (#x).
Definition remove (x : elt) (s : t) := WS.remove (#x) s.
Definition union := WS.union.
Definition inter := WS.inter.
Definition diff := WS.diff.
Definition equal := WS.equal.
Definition subset := WS.subset.
Definition fold {A : Type} := @WS.fold A.
Definition for_all := WS.for_all.
Definition exists_ := WS.exists_.
Definition filter := WS.filter.
Definition partition := WS.partition.
Definition cardinal := WS.cardinal.
Definition elements := WS.elements.
Definition choose := WS.choose.


Definition Inv_function (x : elt) := exists x' : elt, X'.eq (#x') x.
Definition inv_function (x : elt) := false.

Lemma inv_Proper : Proper (X'.eq ==> eq) inv_function.
compute; now auto.
(*
unfold Proper; compute.
 intros x y H.
  destruct X'.eq_dec.
   destruct X'.eq_dec.
    now auto.
    elim n.
     apply X'.eq_equiv with x.
      apply X'.eq_equiv; now auto.
      apply X'.eq_equiv with (#x).
       now auto.
       apply X'.repr_eq.
        apply X'.eq_sub.
         now auto.
   destruct X'.eq_dec.
    elim n.
     apply X'.eq_equiv with y.
      now auto.
      apply X'.eq_equiv with (#y).
       now auto.
       apply X'.eq_equiv; apply X'.repr_eq.
        apply X'.eq_sub.
         now auto.
    now auto.
*)
Qed.


Definition IsOk (s : t) := WS.For_all Inv_function s.

Class Ok (s:t) : Prop := ok : IsOk s.

Ltac unfold_Ok := unfold Ok, IsOk, WS.For_all, Inv_function in *.


Definition isok (s : t) := WS.for_all inv_function s.

Instance isok_Ok (s : t) `(isok s = true) : Ok s.
unfold_Ok; unfold for_all in H.
 intros x HIn.
  apply WS.for_all_spec in H.
   unfold WS.For_all, inv_function in H.
    apply H in HIn.
     now inversion HIn.
   exact inv_Proper.
Qed.


Definition In (x : elt) (s : t) := WS.In (#x) s.

Lemma In_compat : Proper (X.eq ==> Logic.eq ==> iff) In.
unfold Proper; compute.
 intros x y H x0 y0 H'.
  apply WS.In_compat.
   apply X'.repr_eq; now auto.
   now auto.
Qed.

Definition Equal s s' := forall a : elt, In a s <-> In a s'.
Definition Subset s s' := forall a : elt, In a s -> In a s'.
Definition Empty s := forall a : elt, ~ In a s.
Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

Definition eq := Equal.

Instance eq_equiv : Equivalence eq.
unfold eq, Equal, In; constructor.
 unfold Reflexive.
  intros x a; now apply WS.eq_equiv.
 unfold Symmetric; now auto.
 unfold Transitive.
  intros x y z Hl Hr; split; intro H.
   apply Hr; apply Hl; now auto.
   apply Hl; apply Hr; now auto.
Qed.


Instance empty_ok : Ok empty.
unfold_Ok; unfold empty.
 assert (H := WS.empty_spec).
 unfold WS.Empty in H.
  intros x H'; elim H with x; now auto.
Qed.


Instance add_ok (s : t) (x : elt) `{Ok s} : Ok (add x s).
unfold_Ok; unfold add in *.
 intros x' HIn.
  apply WS.add_spec in HIn; destruct HIn as [HIn | HIn].
   exists x; apply X'.eq_equiv.
    now auto.
   now auto.
Qed.

Instance remove_ok (s : t) (x : elt) `{Ok s} : Ok (remove x s).
unfold_Ok; unfold remove in *.
 intros x' HIn.
  apply WS.remove_spec in HIn; destruct HIn as [HIn _]; now auto.
Qed.

Instance singleton_ok (x : elt) : Ok (singleton x).
unfold_Ok; unfold singleton.
 intros x' HIn.
  apply WS.singleton_spec in HIn.
   exists x; apply X'.eq_equiv; now auto.
Qed.

Instance union_ok (s s' : t) `{Ok s, Ok s'} : Ok (union s s').
unfold_Ok; unfold union in *.
 intros x HIn.
  apply WS.union_spec in HIn.
   destruct HIn; now auto.
Qed.

Instance inter_ok (s s' : t) `{Ok s, Ok s'} : Ok (inter s s').
unfold_Ok; unfold inter in *.
 intros x HIn.
  apply WS.inter_spec in HIn.
   destruct HIn; now auto.
Qed.

Instance diff_ok (s s' : t) `{Ok s,Ok s'} : Ok (diff s s').
unfold_Ok; unfold diff in *.
 intros x HIn.
  apply WS.diff_spec in HIn.
   destruct HIn; now auto.
Qed.

Instance filter_ok (s : t) (f : elt -> bool) `{Ok s} : Ok (filter f s).
unfold_Ok; unfold filter in *.
 intros x HIn.
  apply WS.filter_spec' in HIn.
   now auto.
Qed.

Instance partition_ok1 (s : t) (f : elt -> bool) `{Ok s} : Ok (fst (partition f s)).
unfold_Ok; unfold partition in *.
 intros x HIn.
  apply WS.partition_spec1' in HIn.
   now auto.
Qed.

Instance partition_ok2 (s : t) (f : elt -> bool) `{Ok s} : Ok (snd (partition f s)).
unfold_Ok; unfold partition in *.
 intros x HIn.
  apply WS.partition_spec2' in HIn.
   now auto.
Qed.


Lemma mem_spec : forall (s : t) (x : elt) `{Ok s}, (mem x s = true <-> In x s).
intros s x _; unfold mem, In.
 now apply WS.mem_spec.
Qed.

Lemma equal_spec : forall (s s' : t) `{Ok s, Ok s'}, equal s s' = true <-> Equal s s'.
unfold_Ok; unfold equal, Equal, In in *.
 intros s s' O1 O2.
  split; intro H.
   intro a; apply WS.equal_spec; now auto.
   apply WS.equal_spec.
    unfold WS.Equal.
     intro a; split; intro H'.
      assert (X'.eq a (#a)) as Ha by (apply Xspec.repr_exists; auto).
       setoid_rewrite Ha; apply H; setoid_rewrite <- Ha; now auto.
      assert (X'.eq a (#a)) as Ha by (apply Xspec.repr_exists; auto).
       setoid_rewrite Ha; apply H; setoid_rewrite <- Ha; now auto.
Qed.

Lemma subset_spec : forall (s s' : t) `{Ok s, Ok s'}, (subset s s' = true <-> Subset s s').
unfold_Ok; unfold subset, Subset, In in *.
 intros s s' O1 O2.
  split; intro H.
   intro a; apply WS.subset_spec; now auto.
   apply WS.subset_spec.
    unfold WS.Subset.
     intros a H'.
      assert (X'.eq a (#a)) as Ha by (apply Xspec.repr_exists; auto).
       setoid_rewrite Ha; apply H; setoid_rewrite <- Ha; now auto.
Qed.

Lemma empty_spec : Empty empty.
unfold Empty, In, empty.
 intro a; now apply WS.empty_spec.
Qed.

Lemma is_empty_spec : forall (s : t) `{Ok s}, is_empty s = true <-> Empty s.
unfold_Ok; unfold is_empty, Empty, In.
 intros s Hs.
  split; intro Hi.
   intro a; apply WS.is_empty_spec.
    now auto.
   apply WS.is_empty_spec.
    unfold WS.Empty.
     intros a Hi'; apply Hi with a.
      assert (X'.eq a (#a)) as Ha by (apply Xspec.repr_exists; auto).
       setoid_rewrite <- Ha; now auto.
Qed.

Lemma add_spec :
 forall (s : t) (x y : elt) `{Ok s},
  In y (add x s) <-> X.eq y x \/ In y s.
unfold_Ok; unfold In, add.
 intros s x y H; split; intro Hi.
  apply WS.add_spec in Hi.
   destruct Hi as [Hi | Hi].
    left; apply X'.repr_eq; now auto.
    right; now auto.
  apply WS.add_spec.
   destruct Hi.
    left; apply X'.repr_eq; now auto.
    right; now auto.
Qed.

Lemma remove_spec :
 forall (s : t) (x y : elt) `{Ok s},
  In y (remove x s) <-> In y s /\ ~ X.eq y x.
unfold_Ok; unfold remove, In.
 intros s x y H; split; intro Hi.
  apply WS.remove_spec in Hi.
   destruct Hi as [H1 H2]; split.
    now auto.
    contradict H2.
     apply X'.repr_eq; now auto.
  destruct Hi as [H1 H2]; apply WS.remove_spec.
   split.
    now auto.
    contradict H2.
     apply X'.repr_eq; now auto.
Qed.

Lemma singleton_spec : forall x y : elt, In y (singleton x) <-> X.eq y x.
unfold In, singleton; intros x y; split; intro H.
 apply X'.repr_eq; apply WS.singleton_spec; now auto.
 apply WS.singleton_spec; apply X'.repr_eq; now auto.
Qed.

Lemma union_spec :
 forall (s s' : t) (x : elt) `{Ok s, Ok s'},
  In x (union s s') <-> In x s \/ In x s'.
unfold union, In.
 intros s s' x _ _.
  now apply WS.union_spec.
Qed.

Lemma inter_spec :
 forall (s s' : t) (x : elt) `{Ok s, Ok s'},
  In x (inter s s') <-> In x s /\ In x s'.
unfold In, inter.
 intros s s' x _ _.
  now apply WS.inter_spec.
Qed.

Lemma diff_spec :
 forall (s s' : t) (x : elt) `{Ok s, Ok s'},
  In x (diff s s') <-> In x s /\ ~ In x s'.
unfold In, diff.
 intros s s' x _ _.
  now apply WS.diff_spec.
Qed.

Lemma fold_spec :
 forall (s : t) `{Ok s} (A : Type) (i : A) (f : elt -> A -> A),
  fold f s i = fold_left (flip f) (elements s) i.
unfold fold, elements.
 intros s _ A i f; now apply WS.fold_spec.
Qed.

Lemma cardinal_spec : forall (s : t) `{Ok s}, cardinal s = length (elements s).
unfold cardinal, elements.
 intros s _; now apply WS.cardinal_spec.
Qed.


(* Proper function in X.eq is often changed "in X'.eq". *)
Lemma repr_Proper :
 forall f : elt -> bool,
  Proper (X.eq ==> Logic.eq) f ->
   Proper (X'.eq ==> Logic.eq) f.
compute.
 intros f H x y Heq.
  apply H.
   apply X'.eq_sub.
    now auto.
Qed.


(*   apply X.eq_equiv with x.
    apply X.eq_equiv.
     now apply X'.repr_mod.
    apply X.eq_equiv with y.
     apply X'.eq_sub.
      now auto.
     now apply X'.repr_mod.
Qed.
*)

(* Proper function f returns the same value for x and #x. *)
Lemma repr_Proper_eq :
 forall f : elt -> bool,
  Proper (X.eq ==> Logic.eq) f ->
   forall x : elt, f x = f (#x).
compute.
 intros f H x.
  apply H.
   now apply X'.repr_mod.
Qed.


Lemma filter_spec :
 forall (s : t) (x : elt) (f : elt -> bool) `{Ok s},
  Proper (X.eq ==> Logic.eq) f ->
   (In x (filter f s) <-> In x s /\ f x = true).
unfold_Ok; intros s x f Hs Hp; unfold In, filter.
 split; intro H.
  apply WS.filter_spec in H.
   destruct H as [H1 H2]; split.
    now auto.
    rewrite <- H2; apply repr_Proper_eq; now auto.
   apply repr_Proper; now auto.
  apply WS.filter_spec.
   apply repr_Proper; now auto.
   destruct H; split.
    now auto.
    rewrite <- H0; symmetry; now apply repr_Proper_eq.
Qed.

Lemma filter_spec' :
 forall (s : t) (x : elt) (f : elt -> bool) `{Ok s},
  In x (filter f s) -> In x s.
unfold_Ok; unfold In.
 intros s x f _; now apply WS.filter_spec'.
Qed.


Lemma for_all_spec :
 forall (s : t) (f : elt -> bool) `{Ok s},
  Proper (X.eq ==> Logic.eq) f ->
   (for_all f s = true <-> For_all (fun x : elt => f x = true) s).
unfold_Ok; intros s f Hs Hp; unfold In, for_all, WS.For_all, For_all, In.
 split; intro H.
  intros x Hd; apply WS.for_all_spec in H.
   rewrite repr_Proper_eq; now auto.
   apply repr_Proper; now auto.
  apply WS.for_all_spec.
   apply repr_Proper; now auto.
   unfold WS.For_all.
    intros x HIn; assert (X'.eq x (#x)) as Hx by (apply Xspec.repr_exists; auto).
    setoid_rewrite Hx in HIn; now eauto.
Qed.

Lemma exists_spec :
 forall (s : t) (f : elt -> bool) `{Ok s},
  Proper (X.eq ==> Logic.eq) f ->
   (exists_ f s = true <-> Exists (fun x : elt => f x = true) s).
unfold_Ok; intros s f Hs Hp; unfold In, exists_, Exists, WS.Exists, In.
 split; intro H.
  apply WS.exists_spec in H.
   unfold WS.Exists in H.
    destruct H as [x [H1 H2]]; exists x; split; auto.
     assert (X'.eq x (#x)) as Hx by (apply Xspec.repr_exists; auto).
      setoid_rewrite <- Hx; now auto.
   apply repr_Proper; auto.
  apply WS.exists_spec; auto.
   apply repr_Proper; auto.
   unfold WS.Exists.
    destruct H as [x [H1 H2]]; exists (#x); split; auto.
     rewrite <- H2; apply Hp.
      apply X.eq_equiv; now apply X'.repr_mod.
Qed.

Lemma partition_spec1 :
 forall (s : t) (f : elt -> bool) `{Ok s},
  Proper (X.eq ==> Logic.eq) f -> Equal (fst (partition f s)) (filter f s).
intros s f _ Hp.
 apply repr_Proper in Hp.
  unfold Equal, partition, filter.
   intros a; unfold In; apply WS.partition_spec1; now auto.
Qed.

Lemma partition_spec2 :
 forall (s : t) (f : elt -> bool) `{Ok s},
  Proper (X.eq ==> Logic.eq) f ->
   Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s).
intros s f _ Hp.
 apply repr_Proper in Hp.
  unfold Equal, partition, filter.
   intros a; unfold In; apply WS.partition_spec2; now auto.
Qed.


Lemma partition_spec1' :
 forall (s : t) (x : elt) (f : elt -> bool) `{Ok s},
  In x (fst (partition f s)) -> In x s.
intros s x f _; unfold_Ok; unfold In, partition.
 now apply WS.partition_spec1'.
Qed.

Lemma partition_spec2' :
 forall (s : t) (x : elt) (f : elt -> bool) `{Ok s},
  In x (snd (partition f s)) -> In x s.
intros s x f _; unfold_Ok; unfold In, partition.
 now apply WS.partition_spec2'.
Qed.


Lemma elements_spec1 :
 forall (s : t) (x : elt) `{Ok s}, InA X.eq x (elements s) <-> In x s.
intros s x Hs'; unfold In, elements.
 unfold_Ok.
 assert (forall x : elt, InA X'.eq x (WS.elements s) -> exists x' : elt, X'.eq (#x') x) as Hs.
  intros; apply Hs'.
   apply WS.elements_spec1; now auto.
 rewrite <- WS.elements_spec1.
  revert Hs.
   generalize (WS.elements s) as l; clear s Hs'; intros l Hs.
  induction l.
   split; intro H; inversion H.
   repeat rewrite InA_cons.
    assert (forall x : elt, InA X'.eq x l -> exists x' : elt, X'.eq (#x') x) as IH.
     intros; apply Hs.
      rewrite InA_cons; now auto.
    apply IHl in IH.
    assert (X'.eq a (#a)) as Ha.
     apply Xspec.repr_exists.
      apply Hs.
       now constructor.
    split; intro H; destruct H as [H | H].
     left; apply X'.eq_equiv with (#a).
      apply X'.repr_eq; now auto.
      apply X'.eq_equiv; now auto.
     right; apply IH; now auto.
     left; apply X'.repr_eq.
      apply X'.eq_equiv with a; now auto.
     right; apply IH; now auto.
Qed.

Lemma elements_spec2w :
 forall (s : t) `{Ok s}, NoDupA X.eq (elements s).
unfold_Ok; unfold elements; intros s Hs'.
 assert (H := WS.elements_spec2w s).
 assert (forall x : elt, InA X'.eq x (WS.elements s) -> exists x' : elt, X'.eq (#x') x) as Hs.
  intros; apply Hs'; apply WS.elements_spec1; now auto.
 clear Hs'; revert H Hs; generalize (WS.elements s) as l; intros l H Hs.
  induction l.
   now constructor.
   assert (forall x : elt, InA X'.eq x l -> exists x' : elt, X'.eq (#x') x) as IH.
    intros; apply Hs.
     apply InA_cons; now auto.
   assert (X'.eq a (#a)) as Ha.
    apply Xspec.repr_exists.
     apply Hs.
      now constructor.
   inversion H; subst.
    constructor.
     intro H'; apply H2.
      clear -IH H3 Ha H'.
       induction H'.
        apply InA_cons; left.
         assert (X'.eq y (#y)) as Hy.
          apply Xspec.repr_exists.
           apply IH.
            now constructor.
          apply X'.repr_eq in H.
           apply X'.eq_equiv with (#a); auto.
            apply X'.eq_equiv with (#y); auto.
             apply X'.eq_equiv; now auto.
        apply InA_cons; right.
         apply IHH'.
          intros x HIn.
           apply IH.
            apply InA_cons; now auto.
          inversion H3; now auto.
     inversion H; now auto.
Qed.

Lemma choose_spec1 :
 forall (s : t) (x : elt) `{Ok s}, choose s = Some x -> In x s.
unfold_Ok; unfold choose, In; intros s x Hs Hc.
 apply WS.choose_spec1 in Hc.
  assert (X'.eq x (#x)) as Hx by (apply Xspec.repr_exists; auto).
   setoid_rewrite <- Hx; now auto.
Qed.

Lemma choose_spec2 : forall (s : t) `{Ok s}, choose s = None -> Empty s.
unfold_Ok; unfold choose, Empty, In; intros s Hs Hc.
 apply WS.choose_spec2 in Hc.
  unfold WS.Empty in Hc.
   intros a Ha; apply Hc with (#a); now auto.
Qed.


End WRawSetReprWrapper.




Module WSetReprWrapper (X : DecidableType) (X' : DecidableReprType X) (F : WSetsOn) <: WSetsOn X.
Module R := WRawSetReprWrapper X X' F.
Include WRaw2SetsOn X R.
End WSetReprWrapper.



Module MakeWSetRepr (X : DecidableType) (X' : DecidableReprType X) (F : WSetsOn) <: WSets with Module E := X.
Module E := X.
Include WSetReprWrapper X X' F.
End MakeWSetRepr.



