(*
  Определения Теории связей в терминах Теории множеств:

1. Последовательность идентификаторов векторов: L ⊆ ℕ₀.

2. Множество всех векторов идентификаторов длины n ∈ ℕ₀: Vn = Lⁿ.
  Декартова степень Lⁿ всегда даст вектор длины n, так как все его компоненты будут одного и того же типа L.
  Другими словами, Lⁿ представляет собой множество всех возможных n-элементных векторов, где каждый элемент вектора принадлежит множеству L.

3. Множество всех ассоциаций: A = L × Vn.

4. Семейство функций: ∪_f {anetvⁿ | n ∈ ℕ₀} ⊆ A.
Здесь ∪ обозначает объединение всех функций в семействе {anetvⁿ},
 ⊆ обозначает 'это подмножество',
 а A - множество всех ассоциаций.
 Это говорит о том, что все упорядоченные пары, полученные от функций anetvⁿ, являются подмножеством A.

5. Ассоциативная сеть векторов длины n (или n-мерная асеть) из семейства функций {anetvⁿ},
 anetvⁿ : L → Vn отображает идентификатор l из множества L в кортеж идентификаторов длины n,
 который принадлежит множеству Vn, фактически идентифицирует точки в n-мерном пространстве.
 'n' в anetvⁿ указывает на то, что функция возвращает вектора, содержащие n идентификаторов. 

6. Ассоциативная сеть дуплетов (или двумерная асеть): anetp : L → L².

7. Ассоциативная сеть вложенных упорядоченных пар (или иерархическая асеть): anetl : L → P,
 где P = {(∅,∅) | (l,∅) | (l1,l2), l, l1, l2 ∈ L} - это множество вложенных упорядоченных пар,
 которое состоит из пустых пар, пар, содержащих только один элемент, и пар, содержащих два элемента.


  Дополнительные пояснения:

1. Вектор длины n ∈ ℕ₀ можно представить как вложенные упорядоченные пары.

2. Идентификатор вектора - уникальный идентификатор, каждый из которых связан с определенным вектором.

3. Вектор идентификаторов: это вектор, состоящий из нуля или нескольких идентификаторов векторов,
  где количество индексов соответствует количеству элементов вектора.

4. Ассоциация - это упорядоченная пара, состоящая из идентификатора вектора и вектора идентификаторов.
  Эта структура служит для отображения между идентификаторами и векторами или точками в пространстве.

5. Пустой вектор представлен пустым множеством: () представлено как ∅.


  Требования к реализации Теории связей на coq:

1. Использование простых типов с доказанными теоремами в их отношении
2. Использование типа nat для идентификатора вектора
3. Использование типа prod nat для представления упорядоченной пары
4. Использование типа vec для представления векторов идентификаторов
5. Использование типа list для представления ассоциативных сетей
*)

(* Последовательность идентификаторов векторов: L ⊆ ℕ₀ *)
Definition L := nat.

(* Множество векторов идентификаторов длины n ∈ ℕ₀: Vn ⊆ Lⁿ *)
From Coq Require Import Vector.
Definition Vn (n : nat) := t L n.

(* Множество всех ассоциаций: A = L × Vn *)
Definition A (n : nat) := prod L (Vn n).

(* Семейство функций: ∪_n {netⁿ | n ∈ ℕ₀} ⊆ A *)
Definition Net (n : nat) := L -> Vn n.

(* Базовые определения для векторов длины 1 и 2 *)
Definition net1 : Net 1. 

(* ещё не определено *)
Definition net2 : Net 2.


(* net : L → P *)
Definition P := list L.

(* определение "net" может потребовать дальнейшей конкретизации *)
Definition net : L -> P.


(*
  Теорема обертывания и восстановления ассоциативной сети кортежей:

Пусть дана ассоциативная сеть кортежей длины n, обозначенная как netⁿ : L → Tⁿ.
Определим операцию отображения этой сети в ассоциативную сеть вложенных упорядоченных пар net : L → P, где P = {(∅,∅) | (l,∅) | (l1,l2) : l, l1, l2 ∈ L}.
Затем определим обратное отображение из ассоциативной сети вложенных упорядоченных пар обратно в ассоциативную сеть кортежей длины n.

  Теорема утверждает:

Для любой ассоциативной сети кортежей длины n, netⁿ, применение операции преобразования в ассоциативную сеть вложенных упорядоченных пар
 и обратное преобразование обратно в ассоциативную сеть кортежей длины n обеспечивает восстановление исходной сети netⁿ.
То есть, если мы преобразуем netⁿ в net и потом обратно в netⁿ, то мы получим исходную ассоциативную сеть кортежей netⁿ. Иначе говоря:

    ∀ netⁿ : L → Tⁿ, преобразованиеобратно(преобразованиевперед(netⁿ)) = netⁿ.

Это утверждение требуется доказать.
*)


Section NestedPairsNets.
  (* Определение вложенной пары с переменной длиной *)
  Inductive NestedPair: Type :=
  | Empty: NestedPair
  | Doublet: L -> (NestedPair) -> NestedPair.

  (* Определение ассоциативной сети с вложенными парами *)
  Definition NestedPairsNet : Type := L -> NestedPair. 
End NestedPairsNets.

Fixpoint depth (p : NestedPair) : nat :=
  match p with
  | Empty => 0
  | Doublet _ p' => S (depth p')
  end.

Section TuplesNets.
  (* Определение кортежа фиксированной длины n *)
  Fixpoint Tuple (n: nat) : Type :=
    match n with
    | 0 => unit
    | S n' => prod L (Tuple n')
    end.

  (* Определение ассоциативной сети кортежей фиксированной длины n *)
  Definition TuplesNet (n: nat) : Type := L -> Tuple n.
End TuplesNets.

Fixpoint tupleToNestedPair {n: nat} : Tuple n -> NestedPair :=
  match n with
  | 0 => fun _ => Empty
  | S n' => 
      fun t => 
        match t with
        | (f, rest) => Doublet f (tupleToNestedPair rest)
        end
  end.

Definition tuplesNetToPairsNet {n: nat} (f: TuplesNet n) : NestedPairsNet:=
  fun id => tupleToNestedPair (f id).

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

Definition pairsNetToTuplesNetOption {n: nat} (f: NestedPairsNet) : L -> option (Tuple n) :=
  fun id => nestedPairToTupleOption n (f id).

Definition pairsNetToTuplesNet { n: nat } (net: NestedPairsNet) (default: Tuple n) : TuplesNet n :=
  fun id => match nestedPairToTupleOption n (net id) with
            | Some t => t
            | None => default
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

Definition nets_equiv {n: nat} (net1: TuplesNet n) (net2: TuplesNet n) : Prop :=
  forall id, net1 id = net2 id.

(* Теорема обертывания и восстановления ассоциативной сети кортежей *)
Theorem nets_equiv_after_transforms : forall {n: nat} (net: TuplesNet n),
  nets_equiv net (fun id => match nestedPairToTupleOption n ((tuplesNetToPairsNet net) id) with
                            | Some t => t
                            | None   => net id
                            end).
Proof.
  intros n net id.
  unfold tuplesNetToPairsNet.
  simpl.
  rewrite H_inverse.
  reflexivity.
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


