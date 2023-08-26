(*
Определения:
Последовательность идентификаторов кортежей: L ⊆ ℕ₀
Множество кортежей идентификаторов длины n ∈ ℕ₀: Tn ⊆ Lⁿ.
Множество всех ассоциаций: A = L × Tn.
Семейство функций: ∪_n {netⁿ | n ∈ ℕ₀} ⊆ A
Здесь ∪ обозначает объединение всех функций в семействе {netⁿ},
 ⊆ обозначает 'это подмножество',
 а A - множество всех ассоциаций.
 Это говорит о том, что все упорядоченные пары, полученные от функций netⁿ, являются подмножеством A.
Ассоциативная сеть кортежей длины n из семейства функций {netⁿ},
 netⁿ : L → Tn отображает идентификатор l из множества L в кортеж идентификаторов длины n,
 который принадлежит множеству Tn.
 'n' в netⁿ указывает на то, что функция возвращает кортежи, содержащие n идентификаторов. 
Ассоциативная сеть дуплетов: net² : L → T₂.
Ассоциативная сеть вложенных упорядоченных пар: net : L → P,
 где P = {(∅,∅) | (l,∅) | (l1,l2), l, l1, l2 ∈ L} - это множество вложенных упорядоченных пар,
 которое состоит из пустых пар, пар, содержащих только один элемент, и пар, содержащих два элемента.
Дополнительные пояснения:
Кортеж длины n ∈ ℕ₀ можно представить как вложенные упорядоченные пары.
Идентификатор кортежа - уникальный идентификатор, каждый из которых связан с определенным кортежем.
Кортеж идентификаторов - это кортеж, состоящий из нуля или нескольких идентификаторов кортежей,
 где количество индексов соответствует количеству элементов кортежа.
Ассоциация - это упорядоченная пара, состоящая из идентификатора кортежа и кортежа идентификаторов. Эта структура служит для отображения между идентификаторами и кортежами.
Пустой кортеж представлен пустым множеством: () представлено как ∅.

Теорема 2: Пусть n - фиксированное натуральное число, и пусть Tn является множеством кортежей идентификаторов длины n.
 Введем специальный идентификатор l0, которому соответствует пустой дуплет.
 Тогда существует функция f : Tn → P, которая биективно отображает кортеж идентификаторов в вложенную пару,
 и существует функция g : P → D, которая биективно отображает вложенную пару в ассоциативную сеть дуплетов.
 Здесь P - множество вложенных пар, D - сеть дуплетов. 

Словами, это означает, что каждый кортеж идентификаторов фиксированной длины n может быть представлен вложенной парой,
 и каждая вложенная пара может быть представлена ассоциативной сетью дуплетов.
 Отображение в обоих случаях является взаимно однозначным, то есть уникальным в обе стороны.

*)

(* Определяем базовый тип идентификаторов кортежей *)
Definition L := nat.
Definition l0 := 0.

(* Определение кортежа идентификаторов фиксированной длины n *)
Fixpoint Tuple (n: nat) : Type :=
  match n with
  | 0 => unit
  | S n' => prod L (Tuple n')
  end.

Section NestedPairsNets.
  (* Определение вложенной пары с переменной длиной *)
  Inductive NestedPair: Type :=
  | Empty: NestedPair
  | Doublet: L -> (NestedPair) -> NestedPair.

  (* Определение ассоциативной сети вложенных упорядоченных пар *)
  Definition NestedPairsNet : Type := L -> NestedPair. 
End NestedPairsNets.

Fixpoint depth (p : NestedPair) : nat :=
  match p with
  | Empty => 0
  | Doublet _ p' => S (depth p')
  end.

Section DupletNets.  
  (* Определение дуплета *)
  Definition Duplet := prod L L.

  (* Определение ассоциативной сети дуплетов *)
  Definition DupletNet : Type := L -> Duplet.
End DupletNets.

Fixpoint tupleToNestedPair {n: nat} : Tuple n -> NestedPair :=
  match n with
  | 0 => fun _ => Empty
  | S n' => 
      fun t => 
        match t with
        | (f, rest) => Doublet f (tupleToNestedPair rest)
        end
  end.

(* Лемма о сохранении глубины: *)
Lemma depth_preserved : forall {l: nat} (t: Tuple l), depth (tupleToNestedPair t) = l.
Proof.
  intros l. induction l as [| l' IH]; intros t.
  - (* Базовый случай *)
    simpl. reflexivity.
  - (* Шаг индукции *)
    destruct t as [x t']. simpl.
    destruct l'.
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

Fixpoint nestedPairToTupleOption (n: nat) (p: NestedPair) : option (Tuple n) :=
  match n, p with
  | 0, Empty => Some tt
  | S n', Doublet f p' => 
      match nestedPairToTupleOption n' p' with
      | None => None
      | Some t => Some (f, t)
      end
  | _, _ => None
  end.

(* Лемма о взаимном обращении функций nestedPairToTupleOption и tupleToNestedPair *)
Lemma H_inverse: forall n: nat, forall t: Tuple n, nestedPairToTupleOption n (tupleToNestedPair t) = Some t.
Proof.
  intros n. induction n as [| n' IH]; intros t.
  - (* Базовый случай *)
    destruct t. reflexivity.
  - (* Шаг индукции *)
    destruct t as [x t']. simpl.
    rewrite IH. reflexivity.
Qed.

(* Преобразование вложенной пары в DupletNet *)
Fixpoint nestedPairToDupletNet (p: NestedPair) (l: L) : DupletNet :=
  match p with
  | Empty => (fun _ => (l, l0))
  | Doublet l' p' => 
      fun x => if (x =? l) then (l, l') else (nestedPairToDupletNet p' l) x
  end.

(* Преобразование DupletNet во вложенную пару *)
Fixpoint dupletNetToNestedPair (net: DupletNet) (l: L) : NestedPair :=
  match net l with
  | (l', l0) => Empty
  | (l', _) => Doublet l' (dupletNetToNestedPair net l')
  end.

(* Лемма о взаимном обращении функций nestedPairToDupletNet и dupletNetToNestedPair *)
Lemma H_inverse_dupletNet: forall p: NestedPair, forall l: L, dupletNetToNestedPair (nestedPairToDupletNet p l) l = p.
Proof.
  intros p. induction p as [| l' p' IH]; intros l.
  - (* Базовый случай *)
    simpl. reflexivity.
  - (* Шаг индукции *)
    simpl. rewrite IH. reflexivity.
Qed.

(* Теорема 2 *)
Theorem Theorem2: forall n: nat, forall t: Tuple n, forall l: L, dupletNetToNestedPair (nestedPairToDupletNet (tupleToNestedPair t) l) l = tupleToNestedPair t.
Proof.
  intros n t l.
  apply H_inverse_dupletNet.
Qed.



Definition complexExampleNet : TuplesNet 3 :=
  fun id => match id with
  | 0 => (0, (0, (0, tt)))
  | 1 => (1, (1, (0, tt)))
  | 2 => (2, (0, (0, tt)))
  | 3 => (3, (0, (0, tt)))
  | 4 => (4, (0, (0, tt)))
  | S _ => (0, (0, (0, tt)))
  end.

Definition exampleTuple0 : Tuple 0 := tt.
Definition exampleTuple1 : Tuple 1 := (0, tt).
Definition exampleTuple4 : Tuple 4 := (3, (2, (1, (0, tt)))).
Definition nestedPair0 := tupleToNestedPair exampleTuple0.
Definition nestedPair1 := tupleToNestedPair exampleTuple1.
Definition nestedPair4 := tupleToNestedPair exampleTuple4.
Check nestedPair0.
Check nestedPair1.
Check nestedPair4.
Compute nestedPair0.
Compute nestedPair1.
Compute nestedPair4.

Compute (tuplesNetToPairsNet complexExampleNet) 0.
Compute (tuplesNetToPairsNet complexExampleNet) 1.
Compute (tuplesNetToPairsNet complexExampleNet) 2.
Compute (tuplesNetToPairsNet complexExampleNet) 3.
Compute (tuplesNetToPairsNet complexExampleNet) 4.
Compute (tuplesNetToPairsNet complexExampleNet) 5.

Definition testPairsNet : NestedPairsNet :=
  fun _ => Doublet 1 (Doublet 2 (Doublet 0 Empty)).

Definition testTupleDefault : Tuple 3 := (0, (0, (0, tt))). 

Definition testTuplesNet : TuplesNet 3 :=
  pairsNetToTuplesNet testPairsNet testTupleDefault.

Compute testTuplesNet 0.


