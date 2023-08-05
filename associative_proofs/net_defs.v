(*
Определения:
Множество идентификаторов кортежей: L, |L| ≥ 0
Множество идентификаторных кортежей длины n ∈ ℕ₀: Tn ⊆ Lⁿ.
Множество ассоциаций: A ⊆ L × Tn.
Семейство функций: ∪_n {netⁿ | n ∈ ℕ₀} ⊆ A
Здесь ∪ обозначает объединение всех функций в семействе {netⁿ}, ⊆ обозначает "это подмножество", а A - пространство всех ассоциаций. Это говорит о том, что все упорядоченные пары, полученные от функций netⁿ, являются подмножеством A.
Ассоциативная сеть кортежей длины n из семейства функций {netⁿ}, netⁿ : L → Tn отображает идентификатор l из множества L в идентификаторный кортеж длины n, который принадлежит множеству Tn. 'n' в netⁿ указывает на то, что функция возвращает кортежи, содержащие n идентификаторов. 
Ассоциативная сеть дуплетов: net² : L → T₂.
Ассоциативная сеть вложенных упорядоченных пар: net : L → P, где P = {(∅,∅) | (∅,l) | (l1,l2), l, l1, l2 ∈ L} - это множество вложенных упорядоченных пар, которое состоит из пустых пар, пар, содержащих только один элемент, и пар, содержащих два элемента.
Дополнительные пояснения:
Кортеж длины n ∈ ℕ₀ можно представить как вложенные упорядоченные пары.
Идентификатор кортежа - уникальный идентификатор, каждый из которых связан с определенным кортежем.
Идентификаторный кортеж - это кортеж, состоящий из нуля или нескольких идентификаторов кортежей, где количество индексов соответствует количеству элементов кортежа.
Ассоциация - это упорядоченная пара, состоящая из идентификатора кортежа и кортежа идентификаторов. Эта структура служит для отображения между идентификаторами и кортежами.
Пустой кортеж представлен пустым множеством: () представлено как ∅.

Гипотеза 1: Ассоциативная сеть вложенных упорядоченных пар может представлять любую ассоциативную сеть кортежей длины n.
Гипотеза 2: Ассоциативная сеть дуплетов может представлять ассоциативную сеть вложенных упорядоченных пар, только в том случае, если введена специальная ссылка (l = 0) для обозначения пустого кортежа.
Гипотеза 3: Ассоциативная сеть дуплетов может представлять любую ассоциативную сеть.
*)

(* Определяем базовый тип идентификаторов *)
Parameter L: Type.

Section TuplesNets.
  (* Определение кортежа фиксированной длины n *)
  Fixpoint Tuple (n: nat) : Type :=
    match n with
    | 0 => L
    | S n' => (L * (Tuple n'))
    end.

  (* Определение ассоциативная сети кортежей фиксированной длины n *)
  Definition TuplesNet (n: nat) : Type := L -> Tuple n.
End TuplesNets.

Section NestedPairsNets.
  (* Определение вложенной пары с переменной длиной *)
  Inductive NestedPair : Type :=
  | empty : unit -> NestedPair
  | singl : L -> NestedPair
  | nest : L -> NestedPair -> NestedPair.

  (* Определение ассоциативной сети с вложенными парами *)
  Definition NestedPairsNet : Type := L -> NestedPair. 
End NestedPairsNets.

Section DupletNets.  
  (* Определение дуплета *)
  Definition Duplet := prod L L.
  
  (* Определение ассоциативной сети дуплетов *)
  Definition DupletNet : Type := L -> Duplet.
End DupletNets.
(*
Fixpoint tupleToNestedPair {n:nat} : Tuple n -> NestedPair :=
    match n return Tuple n -> NestedPair with
    | O => fun l => singl l 
    | S n => fun t => match t with
          | (l,tail) => nest l (tupleToNestedPair tail)
    end
end.
*)
Fixpoint tupleToNestedPair {n:nat} : Tuple n -> NestedPair :=
    match n with
    | 0 => fun l => singl l
    | S n' => fun t => 
        let (l, tail) := t in
        nest l (tupleToNestedPair tail)
    end.

Definition tuplesNetToPairsNet {n:nat} : TuplesNet n -> NestedPairsNet :=
    fun f id => tupleToNestedPair (f id).

Definition removeLastPair : NestedPair -> (NestedPair * L) :=
    fix rec x :=
    match x with
      | empty _ => (* обработать случай с empty *)
      | singl l => (empty tt, l)
      | nest l' x' => match rec x' with
        | (x'', l'') => (nest l' x'', l'')
        end
  end.
Fixpoint nestedPairToTuple {n:nat} : NestedPair -> option (Tuple n) :=
    match n return NestedPair -> option (Tuple n) with
    | O => fun _ => Some tt 
        | S n => fun p => match removeLastPair p with
        | (rest, l) => match nestedPairToTuple rest with
          | None => None
        | Some t => Some (l,t)
    end
        end
  end.

Definition pairsNetToTuplesNet {n:nat} : NestedPairsNet -> option (TuplesNet n) :=
    fun f => let f' id := nestedPairToTuple (f id) in
    match forall_dec f' with
      | right _ => None
    | left All => Some (fun id => match All id with exist _ t _ => t end)
    end.

Lemma convert_back_and_forth1 {n:nat} (tn: TuplesNet n) : forall id,
        pairsNetToTuplesNet (tuplesNetToPairsNet tn) = Some tn.
Proof.
   unfold pairsNetToTuplesNet, tuplesNetToPairsNet.
   intros.
   (* применяем предикат к функции, которая по определению всегда возвращает Some *)
   destruct (forall_dec (fun id0 => nestedPairToTuple (tupleToNestedPair (tn id0)))).
   + simpl. 
     f_equal.  (* Убеждаемся, что функции соответствуют друг другу *)
     extensionality id'. 
     destruct (All id').  simpl.  (* Распаковываем существующий тип, получаем наше утверждение *)
     generalize (tn id').
     (* здесь начинается реальное свидетельство *)
     induction n; intros t; destruct t.
     - reflexivity. 
     - simpl in e. destruct (removeLastPair (tupleToNestedPair t)). 
       destruct (nestedPairToTuple n0). inversion e.
       specialize (IHn t). rewrite IHn in e. inversion e.
       reflexivity.
   + apply f. clear f. clear id. intros id.
     (* доказываем, что функция всегда возвращает Some *)
     induction n; simpl.
     - reflexivity.
     - destruct (tn id). simpl. destruct (removeLastPair (tupleToNestedPair t)).
       simpl. apply IHn.
Qed.



(*
Section ConversionFunction.
  Require Import List.
  Require Import PeanoNat.

  Inductive NestedPair : Type :=
  | singl : nat -> NestedPair
  | nest : nat -> NestedPair -> NestedPair.

  Fixpoint Tuple (n: nat) : Type :=
    match n with
    | 0 => unit
    | S n' => nat * Tuple n'
    end.

  Fixpoint tupleToNestedPair {n: nat} : Tuple n -> NestedPair :=
    match n with
    | 0 => fun _ => singl 0
    | S n' => fun t => nest (fst t) (tupleToNestedPair (snd t))
    end.

  Definition convertTuplesNetToNestedPairsNet {n: nat} (tn: nat -> Tuple n) : nat -> NestedPair :=
    fun l => tupleToNestedPair (tn l).
End ConversionFunction.

Section ConversionProof.
  Require Import List.
  Require Import PeanoNat.

  Inductive NestedPair : Type :=
  | singl : NestedPair
  | nest : nat -> NestedPair -> NestedPair.

  Fixpoint Tuple (n: nat) : Type :=
    match n with
    | 0 => unit
    | S n' => nat * Tuple n'
    end.

  Fixpoint tupleToNestedPair {n: nat} : Tuple n -> NestedPair :=
    match n with
    | 0 => fun _ => singl
    | S n' => fun t => nest (fst t) (tupleToNestedPair (snd t))
    end.

  Fixpoint nestedPairLength (np : NestedPair) : nat :=
    match np with
    | singl => 0
    | nest _ np' => S (nestedPairLength np')
    end.

  Lemma tupleToNestedPair_keeps_length : forall n (t : Tuple n),
      nestedPairLength (tupleToNestedPair t) = n.
  Proof.
    intros n. induction n; intros t.
    - (* Case n = 0 *)
      simpl. reflexivity.
    - (* Case n = S n' *)
      simpl. f_equal. apply IHn.
  Qed.

  Definition convertTuplesNetToNestedPairsNet {n: nat} (tn: nat -> Tuple n) : nat -> NestedPair :=
    fun l => tupleToNestedPair (tn l).
End ConversionProof.
*)


