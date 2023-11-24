(*
  Определения Теории связей в терминах Теории множеств:

1. Идентификатор вектора - уникальный идентификатор, каждый из которых связан с определенным вектором.
  Последовательность идентификаторов векторов: L ⊆ ℕ₀.

2. Вектор идентификаторов: это вектор, состоящий из нуля или нескольких идентификаторов векторов,
  где количество индексов соответствует количеству элементов вектора.
  Множество всех векторов идентификаторов длины n ∈ ℕ₀: Vn = Lⁿ.
  Декартова степень Lⁿ всегда даст вектор длины n, так как все его компоненты будут одного и того же типа L.
  Другими словами, Lⁿ представляет собой множество всех возможных n-элементных векторов, где каждый элемент вектора принадлежит множеству L.

3. Ассоциация - это упорядоченная пара, состоящая из идентификатора вектора и вектора идентификаторов.
  Эта структура служит для отображения между идентификаторами и векторами или точками в пространстве.
  Множество всех ассоциаций: A = L × Vn.

4. Семейство функций: ∪_f {anetvⁿ | n ∈ ℕ₀} ⊆ A.
  Здесь ∪ обозначает объединение всех функций в семействе {anetvⁿ},
  ⊆ обозначает 'это подмножество', а A - множество всех ассоциаций.
  Это говорит о том, что все упорядоченные пары, полученные от функций anetvⁿ, являются подмножеством A.

5. Ассоциативная сеть векторов длины n (или n-мерная асеть) из семейства функций {anetvⁿ},
  anetvⁿ : L → Vn отображает идентификатор l из множества L в кортеж идентификаторов длины n,
  который принадлежит множеству Vn, фактически идентифицирует точки в n-мерном пространстве.
  'n' в anetvⁿ указывает на то, что функция возвращает вектора, содержащие n идентификаторов. 


6. Дуплет идентификаторов (упорядоченная пара или двухмерный вектор): D = L²
  Это множество всех упорядоченных пар (L, L), или вторая декартова степень L.

7. Ассоциативная сеть дуплетов (или двумерная асеть): anetd : L → L².

8. Пустой вектор представлен пустым множеством: () представлено как ∅.
  Вектор длины n ∈ ℕ₀ можно представить как вложенные упорядоченные пары.

9. Ассоциативная сеть вложенных упорядоченных пар: anetl : L → NP,
  где NP = {(∅,∅) | (l,np), l ∈ L, np ∈ NP} - это множество вложенных упорядоченных пар,
  которое состоит из пустых пар, и пар содержащих один или более элементов.
*)

Require Import Vector.
Require Import List.
Import ListNotations.
Import VectorNotations. (* Import vector notations *)

(* Последовательность идентификаторов векторов: L ⊆ ℕ₀ *)
Definition L := nat.

(* Множество векторов идентификаторов длины n ∈ ℕ₀: Vn ⊆ Lⁿ *)
Definition Vn (n : nat) := t L n.

(* Множество всех ассоциаций: A = L × Vn *)
Definition A (n : nat) := prod L (Vn n).

(* Ассоциативная сеть векторов длины n (или n-мерная асеть) из семейства функций {anetvⁿ : L → Vn} *)
Definition ANetVf (n : nat) := L -> Vn n.
Definition ANetVl (n : nat) := list (Vn n).

(* Дуплет *)
Definition D := prod L L.

(* Ассоциативная сеть дуплетов (или двумерная асеть): anetd : L → L² *)
Definition ANetDf := L -> D.
Definition ANetDl := list D.

(* Вложенные упорядоченные пары *)
Definition NP := list L.

(* Ассоциативная сеть вложенных упорядоченных пар: anetl : L → NP *)
Definition ANetLf := L -> NP.
Definition ANetLl := list NP.

(* Функция преобразования Vn в NP *)
Fixpoint VnToNP {n : nat} (v : Vn n) : NP :=
  match v with
  | Vector.nil _ => List.nil
  | Vector.cons _ h _ t => List.cons h (VnToNP t)
  end.

(* Функция преобразования ANetVf в ANetLf *)
Definition ANetVfToANetLf {n : nat} (a: ANetVf n) : ANetLf:=
  fun id => VnToNP (a id).

(* Лемма о сохранении длины векторов ассоциативной сети *)
Lemma Vn_dim_preserved : forall {l: nat} (t: Vn l), List.length (VnToNP t) = l.
Proof.
  intros l t.
  induction t.
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

(* Функция преобразования NP в Vn *)
Fixpoint NPToVnOption (n: nat) (p: NP) : option (Vn n) :=
  match n, p with
  | 0, List.nil => Some (Vector.nil nat)
  | S n', List.cons f p' => 
      match NPToVnOption n' p' with
      | None => None
      | Some t => Some (Vector.cons nat f n' t)
      end
  | _, _ => None
  end.

(* Функция преобразования ANetLf в условную ANetVf *)
Definition ANetLfToANetVfOption {n: nat} (f: ANetLf) : L -> option (Vn n) :=
  fun id => NPToVnOption n (f id).

(* Функция преобразования ANetLf в ANetVf *)
Definition ANetLfToANetVf { n: nat } (net: ANetLf) (default: Vn n) : ANetVf n :=
  fun id => match NPToVnOption n (net id) with
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
  Теорема обертывания и восстановления ассоциативной сети векторов:

Пусть дана ассоциативная сеть векторов длины n, обозначенная как anetvⁿ : L → Vⁿ.
Определим операцию отображения этой сети в ассоциативную сеть вложенных упорядоченных пар anetl : L → NP, где NP = {(∅,∅) | (l,np), l ∈ L, np ∈ NP}.
Затем определим обратное отображение из ассоциативной сети вложенных упорядоченных пар обратно в ассоциативную сеть векторов длины n.

  Теорема утверждает:

Для любой ассоциативной сети векторов длины n, anetvⁿ, применение операции преобразования в ассоциативную сеть вложенных упорядоченных пар
 и обратное преобразование обратно в ассоциативную сеть векторов длины n обеспечивает восстановление исходной сети anetvⁿ.
То есть, если мы преобразуем anetvⁿ в anetl и потом обратно в anetvⁿ, то мы получим исходную ассоциативную сеть векторов anetvⁿ. Иначе говоря:

    ∀ anetvⁿ : L → Vⁿ, преобразованиеобратно(преобразованиевперед(anetvⁿ)) = anetvⁿ.
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

Definition testPairsNet : NestedPairsNet :=
  fun _ => Doublet 1 (Doublet 2 (Doublet 0 Empty)).

Definition testTupleDefault : Tuple 3 := (0, (0, (0, tt))). 

Definition testTuplesNet : TuplesNet 3 :=
  pairsNetToTuplesNet testPairsNet testTupleDefault.

Compute testTuplesNet 0.


