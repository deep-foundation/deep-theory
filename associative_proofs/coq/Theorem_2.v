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
Require Import Coq.Init.Datatypes.
Require Import PeanoNat.
Import ListNotations.
Import VectorNotations.

(* Последовательность идентификаторов векторов: L ⊆ ℕ₀ *)
Definition L := nat.

(* Дефолтное значение L: ноль *)
Definition LDefault : L := 0.

(* Вложенные упорядоченные пары *)
Definition NP := list L.

Notation "[ ]" := (nil) (at level 0).
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..) (at level 0).

(* Ассоциативная сеть вложенных упорядоченных пар: anetl : L → NP *)
Definition ANetLf := L -> NP.
Definition ANetLl := list NP.

(* Дуплет *)
Definition D := prod L L.

(* Дефолтное значение D: пара из двух LDefault *)
Definition DDefault : D := (LDefault, LDefault).

(* Ассоциативная сеть дуплетов (или двумерная асеть): anetd : L → L² *)
Definition ANetDf := L -> D.
Definition ANetDl := list D.

(* Предикат эквивалентности для ассоциативных сетей дуплетов ANetDf *)
Definition ANetDf_equiv (anet1: ANetDf) (anet2: ANetDf) : Prop := forall id, anet1 id = anet2 id.

(* Предикат эквивалентности для ассоциативных сетей дуплетов ANetDl *)
Definition ANetDl_equiv (anet1: ANetDl) (anet2: ANetDl) : Prop := anet1 = anet2.

(* Функция преобразования NP в ANetDl со явной индексацией *)
Fixpoint NPToANetDl_ (index: L) (np: NP) : ANetDl :=
  match np with
  | nil => nil
  | cons h nil => cons (h, 0) nil
  | cons h t => cons (h, index - 1) (NPToANetDl_ (index - 1) t)
  end.

(* Функция преобразования NP в ANetDl*)
Fixpoint NPToANetDl (np: NP) : ANetDl :=
  match np with
  | nil => nil
  | cons h nil => cons (h, 0) nil
  | cons h t => cons (h, length t) (NPToANetDl t)
  end.

(* Функция добавления NP в ANetDl *)
Definition AddNPToANetDl (anet: ANetDl) (np: NP) : ANetDl :=
  let new_anet := NPToANetDl_ ((length np) + (length anet)) np in
  app new_anet anet.

(* Функция получения дуплета из ANetDl с идентификатором L с дефолтом*)
Definition GetDupletFromANetDl (anet: ANetDl) (index: L) : D :=
  nth_default DDefault anet index.

(* Функция получения дуплета из ANetDl с идентификатором L с опцией*)
Definition GetDupletFromANetDlOption (anet: ANetDl) (index: L) : option D :=
  nth_error anet index.

(* Функция преобразования ANetDl в NP *)
Fixpoint ANetDlToNP_ (anet: ANetDl) (index: L) : NP :=
  match anet with
  | [] => nil
  | cons (x, next_index) tail_anet =>
    if index =? length anet then
      cons x (ANetDlToNP_ tail_anet next_index)
    else
      ANetDlToNP_ tail_anet index
  end.

(* Функция отрезает и возвращает хвост ANetDl заданной длины *)
Fixpoint ANetDl_tail_n (anet: ANetDl) (n : nat) : ANetDl :=
  if n =? (length anet) then
    anet
  else
    if n <? (length anet) then
      match anet with
      | [] => []
      | cons (_, _) t => ANetDl_tail_n t n
      end
    else
      [].

(*
Require Import FunInd.
Require Import Recdef.
Require Import Coq.Wellfounded.Wellfounded.

Function ANetDl_tail_n (anet: ANetDl) (n : nat) {measure length anet} : ANetDl :=
    if n =? (length anet) then
        anet
    else
        if n <? (length anet) then
            match anet with
            | [] => []
            | cons (_, _) t => ANetDl_tail_n t n
            end
        else
        [].
Proof.
  intros.
  destruct anet.
  - simpl. auto.
  - simpl. apply Lt.le_lt_n_Sm. apply Le.le_refl.
Qed.


Function ANetDlToNP (anet: ANetDl) {measure length anet} : NP :=
  match anet with
  | [] => nil
  | cons (x, next_index) tail_anet =>
    cons x (ANetDlToNP (ANetDl_tail_n tail_anet next_index))
  end.
Proof.
  intros. 
  unfold ANetDl_tail_n.
  destruct anet.
  - simpl. auto.
  - rewrite <- teq. simpl. 
    destruct (Nat.ltb next_index (length l)).
    + simpl. apply Lt.le_lt_n_Sm. apply Le.le_refl.
    + auto.
Qed.
*)

(* Функция преобразования ANetDl в NP начиная с головы списка асети
Fixpoint ANetDlToNP (anet: ANetDl) : NP :=
  match anet with
  | [] => nil
  | cons (x, next_index) tail_anet =>
    cons x (ANetDlToNP (ANetDl_tail_n tail_anet next_index))
  end.*)

(* Функция преобразования ANetDl в NP начиная с головы списка асети *)  
Definition ANetDlToNP (anet: ANetDl) : NP := ANetDlToNP_ anet (length anet).


(*  Доказательства *)

(* Лемма о сохранении длины списков NP ассоциативной сети *)
Lemma NP_dim_preserved : forall (np: NP), List.length np = List.length (NPToANetDl np).
Proof.
  intros np.
  induction np as [|h t IH].
  - simpl. reflexivity.
  - destruct t as [|h2 t2].
    + simpl. reflexivity.
    + simpl. apply f_equal. apply IH. 
Qed.


(* Лемма о взаимном обращении функций NPToANetDl и ANetDlToNP

  H_inverse доказывает, что каждый список NP без потери данных может быть преобразован в ANetDl
 с помощью NPToANetDl и обратно в NP с помощью ANetDlToNP.

  В формальном виде forall (np: NP), ANetDlToNP (NPToANetDl np) = np говорит о том,
 что для всякого список NP, мы можем преобразовать NP в ANetDl с помощью NPToANetDl,
 затем обратно преобразовать результат в NP с помощью ANetDlToNP,
 и в итоге получать тот же список NP, что и в начале.

  Это свойство очень важно, потому что оно гарантирует,
 что эти две функции образуют обратные друг к другу пары функций на преобразуемом круге списоке NP и ANetDl.
 Когда вы применяете обе функции к значениям в преобразуемом круге, вы в итоге получаете исходное значение.
 Это означает, что никакая информация не теряется при преобразованиях,
 так что вы можете свободно конвертировать списком NP и ANetDl,
 если это требуется в вашей реализации или доказательствах.
 *)
Theorem NP_ANetDl_NP_inverse: forall (np: NP),
  ANetDlToNP_ (NPToANetDl np) (length np) = np.
Proof.
  intros np.
  induction np as [| h t IH].
  - reflexivity.
  - simpl. 
    case_eq t; intros.  
    + reflexivity. 
    + simpl.
      rewrite NP_dim_preserved. 
      rewrite H in IH.
      reflexivity.
Qed.

Theorem NP_ANetDl_NP_inverse: forall (np: NP),
  ANetDlToNP_ (NPToANetDl np) (length np) = np.
Proof.
  intros np.
  induction np as [| h t IH].
  
  - simpl. reflexivity.  (* базовый случай, когда np пустой *)
   
  - simpl.              (* индуктивный шаг *)
    destruct t as [|h2 t2].
  
    + simpl. reflexivity. (* случай, когда np имеет ровно один элемент *)

    + simpl. 
      rewrite NP_dim_preserved.
      simpl.
      rewrite IH.
      reflexivity.
Qed.


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
(*
Theorem anetf_equiv_after_transforms : forall {n: nat} (anet: ANetVf n),
  ANetVf_equiv anet (fun id => match NPToVnOption n ((ANetVfToANetLf anet) id) with
                            | Some t => t
                            | None   => anet id
                            end).
*)

(*  Примеры *)

Compute NPToANetDl [ 121, 21, 1343 ].
(* Должно вернуть: [(121, 2); (21, 1); (1343, 0)] *)

Compute AddNPToANetDl [(121, 2), (21, 1), (1343, 0)] [12, 23, 34]. 
(* Ожидается результат: [(12, 5), (23, 4), (34, 0), (121, 2), (21, 1), (1343, 0)] *)


Compute ANetDlToNP [(121, 2), (21, 1), (1343, 0)]. 
(* Ожидается результат: [121, 21, 1343] *)

Compute ANetDlToNP [(12, 5), (23, 4), (34, 0), (121, 2), (21, 1), (1343, 0)]. 
(* Ожидается результат: [12, 23, 34] *)

Compute ANetDlToNP_ [(12, 5), (23, 4), (34, 0), (121, 2), (21, 1), (1343, 0)] 6.
(* Ожидается результат: [12, 23, 34] *)

Compute ANetDlToNP_ [(12, 5), (23, 4), (34, 0), (121, 2), (21, 1), (1343, 0)] 3.
(* Ожидается результат: [121, 21, 1343] *)




