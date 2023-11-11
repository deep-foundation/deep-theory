(*
Определения Теории Связей:
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
*)

(*
  Требования к реализации Теории Связей на coq:
1. Использование простых типов с доказанными теоремами в их отношении
  Это необходимо для того, что бы ChatGPT было проще доказывать теоремы для нас.
2. Использование типа nat для идентификатора кортежей
3. Использование типа prod nat для представления типа дуплета
4. Использование типа vec для представления структуры всех ассоциативных сетей как кортежей компонент одного типа
5. Ассоциативная сеть кортежей длины 1 должна иметь такой же тип что и вложенные упорядоченные пары
*)

(*
BinaryRelation - это обобщенный тип для представления упорядоченных пар элементов произвольных типов.
BinaryList - обобщенный тип для представления списков, в которых каждый элемент связан с остатком списка.
Doublet - представляет собой дуплет или упорядоченную пару натуральных чисел.
DupletANet - представляет собой конкретную ассоциативную сеть дуплетов, моделируемую как список дуплетов, где каждый дуплет связан с оставшимся списком. Индекс каждого дуплета в списке становится его идентификатором.
Association - представляет бинарное отношение между натуральным числом (идентификатором) и Doublet. 
*)
Inductive BinaryRelation (A B : Type) : Type :=
  | Rel: A -> B -> BinaryRelation A B.

Definition Doublet := BinaryRelation nat nat.
Definition Association := BinaryRelation nat Doublet.

Inductive BinaryList : Type :=
  | Nil : BinaryList
  | Cons : BinaryRelation Doublet BinaryList -> BinaryList.

Fixpoint BinaryList_depth (d : BinaryList) : nat :=
  match d with
   | Nil => 0
   | Cons (Rel _ d') => S (BinaryList_depth d')
  end.


Definition DupletANet := BinaryList Doublet.


Fixpoint DupletANet_depth (d : DupletANet) : nat :=
  match d with
  | Nil => 0
  | Cons _ t => 1 + (DupletANet_depth t)
  end.

Definition DefaultDoublet := Rel 0 0 : Doublet.

Fixpoint getDoubletAtIndex (l : DupletANet) (i : nat) : Doublet :=
  match l, i with
    | Nil _, _ => DefaultDoublet (* возвращаем стандартное значение если список пуст или i больше длины списка *)
    | Cons _ h t, 0 => h (* возвращаем голову списка, если i = 0 *)
    | Cons _ _ t, S n => getDoubletAtIndex t n (* продолжаем поиск в остатке списка *)
  end.



(*Функция для вычисления глубины Link может быть реализована следующим образом:*)
Fixpoint depthLink (l : Link) : nat :=
  match l with
  | L0 => O (* базовый случай: пустой кортеж, длина равна 0 *)
  | L d nextLink => S (depthLink nextLink) (* рекурсивный случай: добавляем 1 и рекурсивно вызываем функцию для следующего узла *)
  end.

(*Функция для возврата i-го Doublet может быть реализована следующим образом:*)
Fixpoint getDoubletAtIndex (l : Link) (i : nat) : Doublet :=
  match l, i with
  | L0, _ => D0 (* базовый случай: пустой кортеж или случай, когда i выходит за пределы длины кортежа *)
  | L d _, O => d (* базовый случай: найден i-тый дуплет *)
  | L _ nextLink, S j => getDoubletAtIndex nextLink j (* рекурсивный случай: продолжаем поиск в следующем узле *)
  end.

Example exampleTuple : DupletANet := L (D L0 L0) (L (D L0 L0) L0).
Example exampleTuple1 : DupletANet := L (D L0 L0) (L (D L0 L0) L0).
Example exampleTuple2 : DupletANet := L (D L0 L0) (L (D L0 L0) L0).
Compute (DupletANet_depth exampleTuple).
Compute (getDoubletAtIndex exampleTuple 1).

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.

(* Примеры использования:
Definition my_list : list A := cons a (cons b (cons c nil)).
Definition my_vec : vec A n := @Vector.const A n a.
*)

(* Определяем базовый тип идентификаторов *)
Definition L := nat.
Definition l0 := 0.

Section NestedPairsNets.
  (* Определение вложенной пары с переменной длиной *)
  Inductive NestedPair: Type :=
  | Empty: NestedPair
  | Doublet: L -> (NestedPair) -> NestedPair.

  (* Опреледение списка из NestedPair *)
  Definition NestedPairsList : Type := list NestedPair.

  (* Определение интерфейса ассоциативной сети с вложенными парами *)
  Definition INestedPairsNet : Type := L -> NestedPair. 

  (* Определение функции доступа к элементу с номером i в списке *)
  Fixpoint nth_nested_pair (n : nat) (np_list : NestedPairsList) : option NestedPair :=
  match n, np_list with
    | 0, np :: _ => Some np
    | S m, _ :: np_list' => nth_nested_pair m np_list'
    | _, nil => None
  end.

  (* Определение интерфейса ассоциативной сети с вложенными парами на основе list *)
  Definition NestedPairsNetList : Type := list (L * list L).
  Definition IDoubletNetList : L -> list L :=
    fix f i (l : NestedPairsNetList) :=
    match l with
      | nil _ => nil
      | cons (j, ll) l' => if L.eqb i j then ll else f i l'
    end.

  (* Определение интерфейса ассоциативной сети с вложенными парами на основе vec *)
  Definition NestedPairsNetVec : Type := Vector.t (L * list L) n.
  Definition IDoubletNetVec : L -> list L :=
    fix f V i : list L :=
    match V with
      | nil _ => nil
      | cons _ (n:=m) (j, ll) V' =>
    if L.eqb i j then ll else f V' i
    end.

  (* Получение вложенной упорядоченной пары из NestedPairsNetList *)
  Definition getDoubletList (net : NestedPairsNetList) (i : L) : NestedPair :=
    let ll := IDoubletNetList i net in
    match ll with
      | nil => Empty
      | cons hd tl => fold_right Doublet tl Empty
    end.

  (* Получение вложенной упорядоченной пары из NestedPairsNetVec *)
  Definition getDoubletVec (net : NestedPairsNetVec) (i : L) : NestedPair :=
    let ll := IDoubletNetVec net i in
    match ll with
      | nil => Empty
      | cons hd tl => Vector.fold_left (fun p i => Doublet i p) tl (Doublet hd Empty)
    end.
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

Definition tuplesNetToPairsNet {n: nat} (f: TuplesNet n) : INestedPairsNet:=
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

Definition pairsNetToTuplesNetOption {n: nat} (f: INestedPairsNet) : L -> option (Tuple n) :=
  fun id => nestedPairToTupleOption n (f id).

Definition pairsNetToTuplesNet { n: nat } (net: INestedPairsNet) (default: Tuple n) : TuplesNet n :=
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

(*
   Теорема обертывания и восстановления ассоциативной сети кортежей:

Пусть дана ассоциативная сеть кортежей длины n, обозначенная как netⁿ : L → Tⁿ.

Определим операцию отображения этой сети в ассоциативную сеть вложенных упорядоченных пар net : L → P, где P = {(∅,∅) | (l,∅) | (l1,l2) : l, l1, l2 ∈ L}.

Затем определим обратное отображение из ассоциативной сети вложенных упорядоченных пар обратно в ассоциативную сеть кортежей длины n.

  Теорема утверждает:

Для любой ассоциативной сети кортежей длины n, netⁿ, применение операции преобразования в ассоциативную сеть вложенных упорядоченных пар и обратное преобразование обратно в ассоциативную сеть кортежей длины n обеспечивает восстановление исходной сети netⁿ.

То есть, если мы преобразуем netⁿ в net и потом обратно в netⁿ, то мы получим исходную ассоциативную сеть кортежей netⁿ. Иначе говоря:

    ∀ netⁿ : L → Tⁿ, преобразованиеобратно(преобразованиевперед(netⁿ)) = netⁿ.

Это утверждение требуется доказать.
 *)
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

Definition testPairsNet : INestedPairsNet :=
  fun _ => Doublet 1 (Doublet 2 (Doublet 0 Empty)).

Definition testTupleDefault : Tuple 3 := (0, (0, (0, tt))). 

Definition testTuplesNet : TuplesNet 3 :=
  pairsNetToTuplesNet testPairsNet testTupleDefault.

Compute testTuplesNet 0.


