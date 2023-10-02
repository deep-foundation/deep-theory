
(* Определяем базовый тип идентификаторов *)
Definition L := nat.
Definition l0 := 0.


Section TupleNets.
(* Определение кортежа и кортежа идентификаторов *)
Inductive Tuple: Type :=
| EmptyTuple: Tuple
| Tuple2: L -> L -> Tuple.

Inductive TupleId: Type :=
| EmptyTupleId: TupleId
| TupleIdCons: L -> TupleId -> TupleId.

(* Определение множества кортежей идентификаторов длины n *)
Definition TupleIdSet (n: nat): Type :=
{ tupleId : TupleId | lengthTupleId tupleId = n }.

(* Определение ассоциативной сети кортежей *)
Definition TupleNet (n: nat) : Type := L -> TupleIdSet n.

(* Определение семейства функций netⁿ *)
Definition net (n : nat): Type := { net : TupleNet n | True }.

(* Определение преобразования кортежа в вложенную пару и обратно *)
Fixpoint tupleToNestedPair (t: Tuple): NestedPair :=
match t with
| EmptyTuple => Empty
| Tuple2 l1 l2 => Doublet l1 (Doublet l2 Empty)
end.

Fixpoint nestedPairToTuple (p: NestedPair): Tuple:=
match p with
| Empty => EmptyTuple
| Doublet l1 rest =>
match rest with
| Empty => Tuple2 l1 l0
| Doublet l2 rest' => Tuple2 l1 l2
end
end.

(* Определение преобразования ассоциативной сети кортежей в ассоциативную сеть вложенных упорядоченных пар и обратно *)
Fixpoint tupleNetToNestedPairsNetRec {n : nat} (tnet: TupleNet n): NestedPairsNet (S n) :=
match n with
| O => tt
| S n' =>
let rest := tupleNetToNestedPairsNetRec (fun l => TupleIdSet (n')) in
(fun l => tupleToNestedPair (nestedPairToTuple (NestedPairsNetSelect rest l (TupleIdCons l0 EmptyTupleId)))), rest
end.

Definition tupleNetToNestedPairsNet {n: nat} (tnet: TupleNet n) : NestedPairsNet (S n) :=
tupleNetToNestedPairsNetRec tnet.

Fixpoint nestedPairsNetToTupleNetRec {n : nat} (npnet: NestedPairsNet (S n)): TupleNet n :=
match n with
| O => (fun _ => EmptyTupleId)
| S n' =>
let rest := nestedPairsNetToTupleNetRec (snd npnet) in
(fun l =>
let tuple := nestedPairToTuple (NestedPairsNetSelect npnet l) in
match tuple with
| EmptyTuple => EmptyTupleId
| Tuple2 l1 l2 => TupleIdCons l1 (TupleIdCons l2 (proj1_sig (rest l)))
end
)
end.

Definition nestedPairsNetToTupleNet {n: nat} (npnet: NestedPairsNet (S n)) : TupleNet n :=
nestedPairsNetToTupleNetRec npnet.

(* Определение преобразования сети и проверка ее восстановления *)
Definition tupleNetToNet {n: nat} (tnet: TupleNet n) : net n :=
exist _ tnet I.

Definition netToTupleNet {n: nat} (nnet: net n) : TupleNet n :=
proj1_sig nnet.

Theorem netRoundTrip: forall (n : nat) (tnet: TupleNet n),
netToTupleNet (tupleNetToNet tnet) = tnet.
Proof.
intros n tnet.
unfold netToTupleNet, tupleNetToNet.
simpl. unfold proj1_sig. simpl.
unfold tupleNetToNestedPairsNet, nestedPairsNetToTupleNet.
generalize dependent tnet.
induction n.
- intros tnet.
apply functional_extensionality. intros l.
apply extensionality. intros x.
destruct x as [tupleId H]. simpl in H. inversion H.
- intros tnet.
apply functional_extensionality. intros l.
apply extensionality. intros x.
destruct x as [tupleId H].
simpl in H. inversion H.
specialize (IHn (fun l' => TupleIdSet n (TupleIdCons l tupleId))).
simpl.
assert (Tuple2 l l0 = nestedPairToTuple (tupleToNestedPair (Tuple2 l l0))) as H0.
{ reflexivity. }
rewrite H0.
assert (forall (p: NestedPair), Tuple2 (proj1_sig (TupleIdSet_nth tupleId 0)) (proj1_sig (TupleIdSet_nth tupleId 1)) = nestedPairToTuple p ->
((fun l : L =>
tupleToNestedPair
(nestedPairToTuple
(NestedPairsNetSelect
(let
rest := nestedPairsNetToTupleNetRec (snd (tupleNetToNestedPairsNetRec (fun l : L => TupleIdSet n (TupleIdCons l tupleId))))
in
(fun l0 : L =>
tupleToNestedPair
(nestedPairToTuple
(NestedPairsNetSelect
rest l0
(TupleIdCons (proj1_sig (TupleIdSet_nth tupleId 1)) (proj1_sig (TupleIdSet_nth (proj1_sig (rest l0)) 0))) )))))
l) ((fun l : L => TupleIdSet n (TupleIdCons l tupleId)) l))) = tnet)) as H1.
{ intros p H2.
simpl. apply functional_extensionality. intros l'.
destruct (Nat.eqb l l') eqn:E.
- apply Nat.eqb_eq in E. subst. simpl.
match goal with
| [|- context[(let rest := ?rest in ?f)] ] => assert (rest = snd (tupleNetToNestedPairsNetRec (fun l : L => TupleIdSet n (TupleIdCons l tupleId)))) as H3 by reflexivity
end.
rewrite H3.
rewrite (IHn (TupleIdSet_tail tupleId)).
assert ((TupleIdCons (proj1_sig (TupleIdSet_head tupleId)) (TupleIdSetCons (nat:=n) (proj1_sig (TupleIdSet_nth tupleId 1)) (TupleIdSet_tail tupleId))) = tupleId) as H4 by apply TupleIdSet_nth_cons.
simpl in H. rewrite H4 in H.
inversion H. subst. reflexivity.
- simpl. unfold TupleNet. apply functional_extensionality. intros l0.
simpl. apply nestedPairToTuple_injective in H2 as H2'. subst.
match goal with
| [|- tupleToNestedPair ?t = tupleToNestedPair (nestedPairToTuple ?p)] => remember t as t' eqn:Ht'
end.
assert (lengthTuple (nestedPairToTuple p) = 2) as H5 by reflexivity.
simpl in H5. apply f_equal with (f:=@length) in H2'. rewrite <- H2' in H5.
simpl in H5. inversion H5. subst.
match goal with
| [|- context[(let rest := ?rest in ?f)]] => assert (rest = snd (tupleNetToNestedPairsNetRec (fun l : L => TupleIdSetCons (nat:=n) (proj1_sig (TupleIdSet_nth tupleId 1)) (TupleIdSet_tail tupleId)))) as H6 by reflexivity
end.
rewrite H6. rewrite (IHn (fun l : L => TupleIdSetCons (proj1_sig (TupleIdSet_nth p 1)) (TupleIdSet_tail p))).
assert ((TupleIdCons (proj1_sig (TupleIdSet_nth p 0)) (TupleIdSetCons (proj1_sig (TupleIdSet_nth p 1)) (TupleIdSet_tail p))) = p) as H7 by apply TupleIdSet_nth_cons. subst.
reflexivity.
}
apply H1. reflexivity.
Qed.
End TupleNets.