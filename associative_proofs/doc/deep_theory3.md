# Математическое введение в Теорию Связей

## Введение

Данная статья является прямым логическим развитием нашей предыдущей [статьи](https://habr.com/ru/companies/deepfoundation/articles/658705/) и призвана поделиться текущим прогрессом в разработке Теории связей, которую ведет команда Deep.Foundation. В рамках данной статьи будет рассмотрена текущая версия черновика формальной системы "Теории Связей".

* Теория связей разрабатывается как более фундаментальная теория по сравнению с Теорией множеств и Теорий Типов. В то время, как в Теории Типов основными понятиями являются "тип" и "значение", а в Теории Множеств - "множество", "значение", В Теории Связей все сводиться к единому понятию "связь".

В этой статье мы разберем основные понятия и термины, используемые в Теории Связей.

Затем перейдем к определениям Теории Связей в рамках Теории Множеств и представлениям её понятий в ассоциативной сети дуплетов.

Далее рассмотрим, как Теория Связей в том числе ассоциативные числа могут быть представлены в рамках Теории Типов, используя интерактивное программное средство доказательства теорем “Coq”.

В заключении будут подведы итоги и представлены направления дальнейшего исследования и развития Теории Связей.

(Вставить картинку)

## Теория связей

В основе всей Теории связей лежит единое понятие связи.
В Теории связей есть только связи, которые могут играть разные роли и подроли.
Связи могут играть роль ссылки, отношения, ассоциации, контексты, типы, значения, множества, элементы, функции, упорядоченные пары, узлы и ребра и т.д.

### Связь

Связь имеет ассиметричную рекурсивную структуру, которая может быть выражена просто: связь связывает связи.

Связь описывается ачислом (ассоциативным числом), т.е. последовательностью отношений.

Запись связи в виде ачисла, т.е. последовательности ассоциаций убирает прямую рекурсию из её определения.

### Ассоциативная сеть связей

Последовательность связей в ачисле.



## Определения Теории связей в рамках Теории множеств

**Ссылка на вектор** - уникальный идентификатор, каждый из которых связан с определенным вектором.
  Последовательность ссылок на вектора: L ⊆ ℕ₀.

**Вектор ссылок** - это вектор, состоящий из нуля или нескольких ссылок на вектора,
  где количество индексов соответствует количеству элементов вектора.
  Множество всех векторов ссылок длины n ∈ ℕ₀: Vn = Lⁿ.
  Декартова степень Lⁿ всегда даст вектор длины n, так как все его компоненты будут одного и того же типа L.
  Другими словами, Lⁿ представляет собой множество всех возможных n-элементных векторов, где каждый элемент вектора принадлежит последовательности L.

**Ассоциация** - это упорядоченная пара, состоящая из ссылки на вектор и вектора ссылок.
  Эта структура служит для отображения между ссылками и векторами или точками в пространстве.
  Множество всех ассоциаций: A = L × Vn.

**Семейство функций:** ∪_f {anetvⁿ | n ∈ ℕ₀} ⊆ A.
  Здесь ∪ обозначает объединение всех функций в семействе {anetvⁿ},
  ⊆ обозначает 'это подмножество', а A - множество всех ассоциаций.
  Это говорит о том, что все упорядоченные пары, функций anetvⁿ,
  представленных в виде функционального бинарного отношения, являются подмножеством A.

**Ассоциативная сеть векторов длины n** (или n-мерная асеть) из семейства функций {anetvⁿ},
  anetvⁿ : L → Vn отображает ссылку l из последовательности L в вектор ссылок длины n,
  который принадлежит множеству Vn, фактически идентифицирует точки в n-мерном пространстве.
  'n' в anetvⁿ указывает на то, что функция возвращает вектора, содержащие n ссылок.
  Каждая n-мерная асеть таким образом представляет последовательность точек в n-мерная пространстве.

**Дуплет ссылок (упорядоченная пара или двухмерный вектор):** D = L²
  Это множество всех упорядоченных пар (L, L), или вторая декартова степень L.

**Ассоциативная сеть дуплетов (или двумерная асеть):** anetd : L → L².
  Каждая асеть дуплетов таким образом представляет последовательность точек в 2х-мерная пространстве.

**Пустой вектор представлен пустым множеством:** () представлено как ∅.
  Вектор длины n ∈ ℕ₀ можно представить как вложенные упорядоченные пары.

**Ассоциативная сеть вложенных упорядоченных пар:** anetl : L → NP,
  где NP = {(∅,∅) | (l,np), l ∈ L, np ∈ NP} - это множество вложенных упорядоченных пар,
  которое состоит из пустых пар, и пар содержащих один или более элементов.




## Проекция Теории Связей в Теории Типов(Coq) через Теорию Множеств

### Про Coq

Coq — это интерактивное средство для создания доказательств, реализующее Теорию типов высшего порядка, которая известна также как Язык Калькуляции Индуктивных Построений (Calculus of Inductive Constructions, CIC). Это среда обладает возможностями формализации сложных математических теорем, проверки доказательств на корректность, а также извлечения работающего программного кода из формально проверенных спецификаций. Coq широко используется в академических кругах для формализации математики, а также в индустрии для верификации программного обеспечения и оборудования.

Решение применить Coq для описания Теории связей в рамках Теории типов было обусловлено необходимостью строгой формализации доказательств и гарантирования верности логических построений в рамках Теории связей. Использование Coq позволяет выразить свойства и операции над связями в точных и надёжных терминах, благодаря системе типов Coq и мощным средствам для создания и проверки доказательств.

В преддверии обширной работы по доказательству эквивалентности реляционной модели и ассоциативной сети дуплетов, мы представляем в этом разделе начальные шаги выполненные с использованием системы доказательств Языка Coq. На первом этапе стоит задача формализации структур ассоциативных сетей через определения базовых типов функций и структур внутри Coq.

### Определения ассоциативных сетей на Coq

```coq
(* Последовательность ссылок на вектора: L ⊆ ℕ₀ *)
Definition L := nat.

(* Дефолтное значение L: ноль *)
Definition LDefault : L := 0.

(* Множество векторов ссылок длины n ∈ ℕ₀: Vn ⊆ Lⁿ *)
Definition Vn (n : nat) := t L n.

(* Дефолтное значение Vn *)
Definition VnDefault (n : nat) : Vn n := Vector.const LDefault n.

(* Множество всех ассоциаций: A = L × Vn *)
Definition A (n : nat) := prod L (Vn n).

(* Ассоциативная сеть векторов длины n (или n-мерная асеть) из семейства функций {anetvⁿ : L → Vn} *)
Definition ANetVf (n : nat) := L -> Vn n.

(* Ассоциативная сеть векторов длины n (или n-мерная асеть) в виде последовательности *)
Definition ANetVl (n : nat) := list (Vn n).

(* Вложенные упорядоченные пары *)
Definition NP := list L.

(* Ассоциативная сеть вложенных упорядоченных пар: anetl : L → NP *)
Definition ANetLf := L -> NP.

(* Ассоциативная сеть вложенных упорядоченных пар в виде последовательности вложенных упорядоченных пар *)
Definition ANetLl := list NP.

(* Дуплет ссылок *)
Definition D := prod L L.

(* Дефолтное значение D: пара из двух LDefault, используется для обозначения пустого дуплета *)
Definition DDefault : D := (LDefault, LDefault).

(* Ассоциативная сеть дуплетов (или двумерная асеть): anetd : L → L² *)
Definition ANetDf := L -> D.

(* Ассоциативная сеть дуплетов (или двумерная асеть) в виде последовательности дуплетов *)
Definition ANetDl := list D.
```

```coq
(* Функция преобразования Vn в NP *)
Fixpoint VnToNP {n : nat} (v : Vn n) : NP :=
  match v with
  | Vector.nil _ => List.nil
  | Vector.cons _ h _ t => List.cons h (VnToNP t)
  end.

(* Функция преобразования ANetVf в ANetLf *)
Definition ANetVfToANetLf {n : nat} (a: ANetVf n) : ANetLf:=
  fun id => VnToNP (a id).

(* Функция преобразования ANetVl в ANetLl *)
Definition ANetVlToANetLl {n: nat} (net: ANetVl n) : ANetLl :=
  map VnToNP net.

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

(* Функция преобразования NP в Vn с VnDefault *)
Definition NPToVn (n: nat) (p: NP) : Vn n :=
  match NPToVnOption n p with
  | None => VnDefault n
  | Some t => t
  end.

(* Функция преобразования ANetLf в ANetVf *)
Definition ANetLfToANetVf { n: nat } (net: ANetLf) : ANetVf n :=
  fun id => match NPToVnOption n (net id) with
            | Some t => t
            | None => VnDefault n
            end.

(* Функция преобразования ANetLl в ANetVl *)
Definition ANetLlToANetVl {n: nat} (net : ANetLl) : ANetVl n :=
  map (NPToVn n) net.

(* Определение anets_equiv вводит предикат эквивалентности двух ассоциативных сетей векторов длины n,
 anet1 и anet2 типа ANetVf. 

  Данный предикат описывает свойство "эквивалентности" для таких сетей.
 Он утверждает, что anet1 и anet2 считаются "эквивалентными", если для каждой ссылки id вектор,
 связанный с id в anet1, точно совпадает с вектором, связанным с тем же id в anet2.
*)
Definition ANetVf_equiv {n: nat} (anet1: ANetVf n) (anet2: ANetVf n) : Prop :=
  forall id, anet1 id = anet2 id.

(* Определение anets_equiv вводит предикат эквивалентности двух ассоциативных сетей векторов длины n,
 anet1 и anet2 типа ANetVl.
*)
Definition ANetVl_equiv_Vl {n: nat} (anet1: ANetVl n) (anet2: ANetVl n) : Prop :=
  anet1 = anet2.

(*  Доказательства *)

(* Лемма о сохранении длины векторов ассоциативной сети *)
Lemma Vn_dim_preserved : forall {l: nat} (t: Vn l), List.length (VnToNP t) = l.
Proof.
  intros l t.
  induction t.
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

(* Лемма о взаимном обращении функций NPToVnOption и VnToNP

  H_inverse доказывает, что каждый вектор Vn без потери данных может быть преобразован в NP
 с помощью VnToNP и обратно в Vn с помощью NPToVnOption.

  В формальном виде forall n: nat, forall t: Vn n, NPToVnOption n (VnToNP t) = Some t говорит о том,
 что для всякого натурального числа n и каждого вектора Vn длины n,
 мы можем преобразовать Vn в NP с помощью VnToNP,
 затем обратно преобразовать результат в Vn с помощью NPToVnOption n,
 и в итоге получать тот же вектор Vn, что и в начале.

  Это свойство очень важно, потому что оно гарантирует,
 что эти две функции образуют обратные друг к другу пары функций на преобразуемом круге векторов Vn и NP.
 Когда вы применяете обе функции к значениям в преобразуемом круге, вы в итоге получаете исходное значение.
 Это означает, что никакая информация не теряется при преобразованиях,
 так что можно свободно конвертировать между Vn и NP,
 если это требуется в реализации или доказательствах.
 *)
Lemma H_inverse: forall n: nat, forall t: Vn n, NPToVnOption n (VnToNP t) = Some t.
Proof.
  intros n.
  induction t as [| h n' t' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(*
  Теорема обертывания и восстановления ассоциативной сети векторов:

Пусть дана ассоциативная сеть векторов длины n, обозначенная как anetvⁿ : L → Vⁿ.
Определим операцию отображения этой сети в ассоциативную сеть вложенных упорядоченных пар anetl : L → NP,
  где NP = {(∅,∅) | (l,np), l ∈ L, np ∈ NP}.
Затем определим обратное отображение из ассоциативной сети вложенных упорядоченных пар обратно в ассоциативную сеть векторов длины n.

  Теорема утверждает:

Для любой ассоциативной сети векторов длины n, anetvⁿ, применение операции преобразования в ассоциативную сеть вложенных упорядоченных пар
 и обратное преобразование обратно в ассоциативную сеть векторов длины n обеспечивает восстановление исходной сети anetvⁿ.
То есть, если мы преобразуем anetvⁿ в anetl и потом обратно в anetvⁿ, то мы получим исходную ассоциативную сеть векторов anetvⁿ.
 Иначе говоря:

    ∀ anetvⁿ : L → Vⁿ, преобразованиеобратно(преобразованиевперед(anetvⁿ)) = anetvⁿ.
*)

Theorem anetf_equiv_after_transforms : forall {n: nat} (anet: ANetVf n),
  ANetVf_equiv anet (fun id => match NPToVnOption n ((ANetVfToANetLf anet) id) with
                            | Some t => t
                            | None   => anet id
                            end).
Proof.
  intros n net id.
  unfold ANetVfToANetLf.
  simpl.
  rewrite H_inverse.
  reflexivity.
Qed.


(*  Примеры *)

Definition complexExampleNet : ANetVf 3 :=
  fun id => match id with
  | 0 => [0; 0; 0]
  | 1 => [1; 1; 2]
  | 2 => [2; 4; 0]
  | 3 => [3; 0; 5]
  | 4 => [4; 1; 1]
  | S _ => [0; 0; 0]
  end.

Definition exampleTuple0 : Vn 0 := [].
Definition exampleTuple1 : Vn 1 := [0].
Definition exampleTuple4 : Vn 4 := [3; 2; 1; 0].
Definition nestedPair0 := VnToNP exampleTuple0.
Definition nestedPair1 := VnToNP exampleTuple1.
Definition nestedPair4 := VnToNP exampleTuple4.
Check nestedPair0.
Check nestedPair1.
Check nestedPair4.
Compute nestedPair0.
Compute nestedPair1.
Compute nestedPair4.

Compute (ANetVfToANetLf complexExampleNet) 0.
Compute (ANetVfToANetLf complexExampleNet) 1.
Compute (ANetVfToANetLf complexExampleNet) 2.
Compute (ANetVfToANetLf complexExampleNet) 3.
Compute (ANetVfToANetLf complexExampleNet) 4.
Compute (ANetVfToANetLf complexExampleNet) 5.

Definition testPairsNet : ANetLf :=
  fun _ => cons 1 (cons 2 (cons 0 nil)).

Definition testTuplesNet : ANetVf 3 :=
  ANetLfToANetVf testPairsNet.

Compute testTuplesNet 0.

(* Предикат эквивалентности для ассоциативных сетей дуплетов ANetDf *)
Definition ANetDf_equiv (anet1: ANetDf) (anet2: ANetDf) : Prop := forall id, anet1 id = anet2 id.

(* Предикат эквивалентности для ассоциативных сетей дуплетов ANetDl *)
Definition ANetDl_equiv (anet1: ANetDl) (anet2: ANetDl) : Prop := anet1 = anet2.

(* Функция преобразования NP в ANetDl со смещением индексации *)
Fixpoint NPToANetDl_ (offset: nat) (np: NP) : ANetDl :=
  match np with
  | nil => nil
  | cons h nil => cons (h, offset) nil
  | cons h t => cons (h, S offset) (NPToANetDl_ (S offset) t)
  end.

(* Функция преобразования NP в ANetDl*)
Definition NPToANetDl (np: NP) : ANetDl := NPToANetDl_ 0 np.

(* Функция добавления NP в хвост ANetDl *)
Definition AddNPToANetDl (anet: ANetDl) (np: NP) : ANetDl :=
  app anet (NPToANetDl_ (length anet) np).

(* Функция отрезает голову anetd и возвращает хвост начиная с offset  *)
Fixpoint ANetDl_behead (anet: ANetDl) (offset : nat) : ANetDl :=
  match offset with
  | 0 => anet
  | S n' =>
    match anet with
    | nil => nil
    | cons h t => ANetDl_behead t n'
    end
  end.

(* Функция преобразования ANetDl в NP с индексации в начале ANetDl начиная с offset*)
Fixpoint ANetDlToNP_ (anet: ANetDl) (offset: nat) (index: nat): NP :=
  match anet with
  | nil => nil
  | cons (x, next_index) tail_anet =>
    if offset =? index then
      cons x (ANetDlToNP_ tail_anet (S offset) next_index)
    else
      ANetDlToNP_ tail_anet (S offset) index
  end.

(* Функция чтения NP из ANetDl по индексу дуплета*)
Definition ANetDl_readNP (anet: ANetDl) (index: nat) : NP :=
  ANetDlToNP_ anet 0 index.

(* Функция преобразования ANetDl в NP начиная с головы списка асети *)  
Definition ANetDlToNP (anet: ANetDl) : NP := ANetDl_readNP anet 0.


(*  Доказательства *)

(* Лемма о сохранении длины списков NP в ассоциативной сети дуплетов *)
Lemma NP_dim_preserved : forall (offset: nat) (np: NP), 
    length np = length (NPToANetDl_ offset np).
Proof.
  intros offset np.
  generalize dependent offset. 
  induction np as [| n np' IHnp']; intros offset.
  - simpl. reflexivity.
  - destruct np' as [| m np'']; simpl; simpl in IHnp'.
    + reflexivity.
    + rewrite IHnp' with (offset := S offset). reflexivity.
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
*)

Notation "{ }" := (nil) (at level 0).
Notation "{ x , .. , y }" := (cons x .. (cons y nil) ..) (at level 0).
```

```coq
(*  Примеры *)

Compute NPToANetDl { 121, 21, 1343 }.
(* Должно вернуть: {(121, 1), (21, 2), (1343, 2)} *)

Compute AddNPToANetDl {(121, 1), (21, 2), (1343, 2)} {12, 23, 34}. 
(* Ожидается результат: {(121, 1), (21, 2), (1343, 2), (12, 4), (23, 5), (34, 5)} *)


Compute ANetDlToNP {(121, 1), (21, 2), (1343, 2)}. 
(* Ожидается результат: {121, 21, 1343} *)

Compute ANetDlToNP {(121, 1), (21, 2), (1343, 2), (12, 4), (23, 5), (34, 5)}. 
(* Ожидается результат: {121, 21, 1343} *)

Compute ANetDl_readNP {(121, 1), (21, 2), (1343, 2), (12, 4), (23, 5), (34, 5)} 0.
(* Ожидается результат: {121, 21, 1343} *)

Compute ANetDl_readNP {(121, 1), (21, 2), (1343, 2), (12, 4), (23, 5), (34, 5)} 3.
(* Ожидается результат: {12, 23, 34} *)


(*
  Теперь всё готово для преобразования асети вложенных упорядоченных пар anetl : L → NP
в асеть дуплетов anetd : L → L².

Данное преобразование можно делать по разному: с сохранением исходных ссылок на вектора
либо с переиндексацией. Переиндексацию можно не делать если написать дополнительную функцию для
асети дуплетов которая возвращает вложенную упорядоченную пару по её ссылке.
*)

(* Функция добавления ANetLl в ANetDl *)
Fixpoint AddANetLlToANetDl (anetd: ANetDl) (anetl: ANetLl) : ANetDl :=
  match anetl with
  | nil => anetd
  | cons h t => AddANetLlToANetDl (AddNPToANetDl anetd h) t
  end.

(* Функция преобразования ANetLl в ANetDl *)
Definition ANetLlToANetDl (anetl: ANetLl) : ANetDl :=
  match anetl with
  | nil => nil
  | cons h t => AddANetLlToANetDl (NPToANetDl h) t
  end.


(* Функция поиска NP в хвосте ANetDl начинающемуся с offset по её порядковому номеру. Возвращает offset NP *)
Fixpoint ANetDl_offsetNP_ (anet: ANetDl) (offset: nat) (index: nat) : nat :=
  match anet with
  | nil => offset + (length anet)
  | cons (_, next_index) tail_anet =>
    match index with
    | O => offset
    | S index' => 
      if offset =? next_index then
        ANetDl_offsetNP_ tail_anet (S offset) index'
      else
        ANetDl_offsetNP_ tail_anet (S offset) index
    end
  end.


(* Функция поиска NP в ANetDl по её порядковому номеру. Возвращает offset NP *)
Definition ANetDl_offsetNP (anet: ANetDl) (index: nat) : nat :=
  ANetDl_offsetNP_ anet 0 index.

(* Функция преобразования ANetVl в ANetDl *)
Definition ANetVlToANetDl {n : nat} (anetv: ANetVl n) : ANetDl :=
  ANetLlToANetDl (ANetVlToANetLl anetv).


(*
  Теперь всё готово для преобразования асети дуплетов anetd : L → L²
 в асеть вложенных упорядоченных пар anetl : L → NP

Данное преобразование будем делать с сохранением исходных ссылоке на вектора.
Переиндексацию можно не делать, потому что есть функция ANetDl_offsetNP для
асети дуплетов которая возвращает смещение вложенной УП по ссылке на её.
*)

(* Функция отрезает первую NP из ANetDl и возвращает хвост *)
Fixpoint ANetDl_beheadNP (anet: ANetDl) (offset: nat) : ANetDl :=
  match anet with
  | nil => nil
  | cons (_, next_index) tail_anet =>
    if offset =? next_index then (* конец NP *)
      tail_anet
    else  (* ещё не конец NP *)
      ANetDl_beheadNP tail_anet (S offset)
  end.

(* Функция преобразования NP и ANetDl со смещения offset в ANetLl *)
Fixpoint ANetDlToANetLl_ (anetd: ANetDl) (np: NP) (offset: nat) : ANetLl :=
  match anetd with
  | nil => nil (* отбрасываем NP даже если она недостроена *)
  | cons (x, next_index) tail_anet =>
    if offset =? next_index then (* конец NP, переходим к следующей NP *)
      cons (app np (cons x nil)) (ANetDlToANetLl_ tail_anet nil (S offset))
    else  (* ещё не конец NP, парсим асеть дуплетов дальше *)
      ANetDlToANetLl_ tail_anet (app np (cons x nil)) (S offset)
  end.


(* Функция преобразования ANetDl в ANetLl *)
Definition ANetDlToANetLl (anetd: ANetDl) : ANetLl :=
  ANetDlToANetLl_ anetd nil LDefault.


(*  Примеры *)

Definition test_anetl := { {121, 21, 1343}, {12, 23}, {34}, {121, 21, 1343}, {12, 23}, {34} }.
Definition test_anetd := ANetLlToANetDl test_anetl.

Compute test_anetd.
(* Ожидается результат:
 {(121, 1), (21, 2), (1343, 2),
  (12, 4), (23, 4),
  (34, 5),
  (121, 7), (21, 8), (1343, 8),
  (12, 10), (23, 10),
  (34, 11)} *)


Compute ANetDl_offsetNP test_anetd 0.
Compute ANetDl_offsetNP test_anetd 1.
Compute ANetDl_offsetNP test_anetd 2.
Compute ANetDl_offsetNP test_anetd 3.
Compute ANetDl_offsetNP test_anetd 4.
Compute ANetDl_offsetNP test_anetd 5.
Compute ANetDl_offsetNP test_anetd 6.
Compute ANetDl_offsetNP test_anetd 7.

Definition test_anetv : ANetVl 3 :=
  { [0; 0; 0], [1; 1; 2], [2; 4; 0], [3; 0; 5], [4; 1; 1], [0; 0; 0] }.

Compute ANetVlToANetDl test_anetv.

Compute test_anetd.
(* Ожидается результат:
 {(121, 1), (21, 2), (1343, 2),
  (12, 4), (23, 4),
  (34, 5),
  (121, 7), (21, 8), (1343, 8),
  (12, 10), (23, 10),
  (34, 11)} *)

Compute ANetDlToANetLl test_anetd.

Definition test_anetdl : ANetDl := ANetVlToANetDl test_anetv.

Definition result_TuplesNet : ANetVl 3 :=
  ANetLlToANetVl (ANetDlToANetLl test_anetdl).

Compute result_TuplesNet.
```


## Практическая реализация

Deep – это система, основанная на Теории Связи. В Теории Связей с помощью связей можно представлять любые данные или знания, а также использовать их для программирования. На это и ореинтирован Deep. Код в Deep загружается из ассоциативного хранилища в контейнеры Docker и безопасно выполняется. Вся коммуникация между различными частями кода осуществляется через связи в базе данных, что делает базу данных универсальным обменником данных.

Deep позволяет делать весь софт на планете совместимым, представляя все его части ввиде связей. Также возможно хранить любые данные и код вместе, связывать типы ассоциаций событий с соответствующим кодом, который выполняется для обработки этих событий. Каждый обработчик может выбирать связи из базы данных и вставлять/обновлять/удалять связи в базе данных, что может инициировать дальнейшее выполнение обработчиков.

Таблица links в базе данных Deep содержит записи, которые можно интерпретировать как связи. Они имеют такие колонки как id, type_id, from_id, и to_id. Типы связей помогают определить семантику отношений между различными элементами. Кроме таблицы links, в системе также присутствуют таблицы numbers, strings и objects для хранения числовых, строковых и JSON-данных соответственно.


## Заключение

### Выводы

### Планы на будущее

P.S. Статья будет обновляться по мере развития и дополнения Теории Связи в течение следующего месяца.
