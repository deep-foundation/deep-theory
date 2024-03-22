# Математическое введение в Теорию Связей

Эта статья является продолжением нашей прошлой [статьи](https://habr.com/ru/companies/deepfoundation/articles/658705/).

## Введение

В данной статье будер разобрана концепция математической Теории Связи. Будет разобрана сама концепция и основные определения, термины. Также рассмотрим описание Теории Связей в рамках терминов Теории Множества и Теории Типов - с использованием языка автоматизированных доказательств “coq”.




(Вставить картинку)

В этой статье будет представлен черновик концепции теории связей,
который мы опишем в терминах теории множеств и теории типов с применением Coq.

## Теория связей

### Связь

### Сеть связей

### Роли связей

Ссылка
Ассоциация (элемент ФБО описывающий сопоставление прообраза образу)
Значение (Упорядоченна пара)
Контекст

### Последовательность

### Ассоциативное число

Ассоциативная теория основана на концепции связи.

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


### Представление функций в ассоциативной сети дуплетов

Связи хранимые в АСД могут играть разные роли, позволяя описывать различные математические структуры Теории Множеств. 
Рассмотрим пример того как связи могут представлять ФБО (функциональное бинарное отношение), т.е. описание функций.

  
1. ФА (функция агрегирования) - это правило или процедура, которая каждому конкретному элементу сопоставляет определённое множество,
 и таким образом ФА описывает состав множества.

2. БО (бинарное отношение) можно рассматривать как подмножество ПП (прямого произведения) двух множеств.
  Таким образом, УП (упорядоченные пары), составляющие это БО, являются элементами множества, описывающего данное отношение.

3. Сопоставление элемента к соответствующему множеству в рамках ФА можно представить в виде УП (элемент, множество).
  Таким образом, ФА, описывающая множество, может быть представлена как ФБО, где каждая УП уникально сопоставляет элемент и его агрегирующее множество.

4. Если мы имеем несколько ФА, каждая из которых определяется своим ФБО,
  то один и тот же элемент может быть сопоставлен разным множествам в рамках разных ФА.

5. Исходя из предыдущих утверждений, УП (элемент, множество) может сама по себе рассматриваться как элемент в контексте ФА.
  Сама ФА, представляющая набор таких упорядоченных пар, может рассматриваться как множество.
  Таким образом, ФА можно описать и интерпретировать как специфическое множество в рамках ТМ.

6. Исходя из определения ФА как множества УП, каждое такое множество можно интерпретировать как ФА,
  где каждый элемент этого множества является УП (элемент, множество). Далее, каждая такая УП интерпретируется как элемент.
  Это утверждение отражает, что в контексте ТМ, функции и элементы можно интерпретировать в рамках друг друга.

#### 1: состав множества можно описать ФА, представленной в виде ФБО состоящего из УП типа (элемент, множество).

#### 2: ФА так же может описывать множество ФА, как ФБО состоящее из УП типа (УП, ФА).

#### 3: Т.к. ФА так же может описывать множество ФА, как ФБО состоящее из УП типа (УП, ФА),
  то для описания одной ФА достаточно наличия хотя бы одной УП типа (УП, ФА),
  таким образом ФА может идентифицировать УП типа (УП, ФА).

#### 4: ФА может самоопределить себя одной УП


## Описание Теории связей в рамках Теории множеств

* Написать что такое coq.
* Напичать про доказательства теории связей на coq.

### Определения ассоциативных сетей на coq

Последовательность ссылок на вектора: L ⊆ ℕ₀

```coq
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

### Определение типа ассоциативного числа в coq

```coq
(* 
  `anum` - это индуктивный тип в Coq для представления ассоциативного числа, который является расширением чисел Пеано:
  Они могут быть использован для представления различных структур данных и вычислений,
  включая натуральные числа, списки, деревья, графы и ассоциативные сети кортежей.

- Натуральные числа: конструкторы `E` и `L` повторяют стандартную конструкцию натуральных чисел в Coq.
  При этом `E` представляет ноль, а `L` увеличивает число на единицу.

- Фрактальные списки или древовидные структуры: конструктор `A` принимает два значения типа `anum` и ассоциирует их вместе,
  создавая вложенную структуру. Таким образом, `anum` может представлять древовидные структуры,
  где `A` используется для создания узлов дерева, а `E` и `L` используются для представления листьев.

- Фрактальные структуры: благодаря рекурсивной природе `anum`, он может представлять фрактальные структуры.
  Каждый узел, созданный с помощью `A`, может содержать другие значения `anum`,
  которые сами могут быть деревьями, созданными с помощью `A`. Таким образом,
  `anum` может представлять собой отношение самоподобия и вложенности, характерное для фракталов.

- В контексте графа, например, `A` мог бы быть использован для представления ребра между двумя вершинами.

Обратите внимание, что поведение и свойства `anum` будут зависеть от конкретных сценариев использования и интерпретации,
которую вы присваиваете каждому из конструкторов `E`, `L`, `A`.
*)
Inductive anum : Type :=
  | E : anum
  | L : anum -> anum
  | A : anum -> anum -> anum. 


(* 
  Функция `init_anet0` - это функция инициализации списка,
  которая создает чистую ассоциативную сеть нульплетов заданной длины,
  т.е. создает пустой список заданной длины. 
*)
Fixpoint init_anet0 (n : nat) : anum :=
match n with 
| 0 => E
| S n' => L (init_anet0 n')
end.


(* 
  Функция `init_anet1` - это функция инициализации списка, которая создает чистую ассоциативную сеть синглетов заданной длины. 
  Каждый индекс списка представлен как `E` (то есть число `0`).
*)
Fixpoint init_anet1 (n : nat) : anum :=
match n with 
| 0 => E
| S n' => A E (init_anet1 n')
end.


(* 
  Функция `init_anet2` - это функция инициализации списка, которая создает чистую ассоциативную дуплет заданной длины. 
  Каждый элемент списка представлен как `A E E` (то есть дуплет из пары `0`).
*)
Fixpoint init_anet2 (n : nat) : anum :=
match n with 
| 0 => E
| S n' => A (A E E) (init_anet2 n')
end.


(* 
  Функция init_anet_with создаёт anum длины n, где каждый элемент представлен как a.
  Если n равно 0, функция вернёт E. В противном случае, она создаст anum,
  который начинается с a и рекурсивно включает остальные элементы, полученные вызовом init_anet_with.
*)
Fixpoint init_anet_with (n : nat) (a : anum) : anum :=
match n with 
| 0 => E
| S n' => A a (init_anet_with n' a)
end.


(* 
  Функция `get_dim` вычисляет размерность или "вложенность" `anum`.
  Обратите внимание, что это всего лишь одна из возможных метрик "глубины" или "размера" `anum`, 
  и конкретный выбор функции будет зависеть от вашего приложения или модели.
*)
Fixpoint get_dim (a : anum) : nat :=
match a with
| E => 0
| L a' => 0
| A a' _ => 1 + get_dim a'
end.


(* 
  Функция `get_size` вычисляет глубину `anum` или длину списка воспринимая его как последовательность аналогичную nat.
*)
Fixpoint get_size (a : anum) : nat :=
match a with
| E => 0
| L a1 => S (get_size a1)
| A _ a2 => S (get_size a2)
end.


(* 
  Функция `concat` принимает два значения типа `anum`,
  которые представляют собой списки, и возвращает их
  конкатенацию – один список, который начинается
  с элементов первого списка и продолжается элементами второго.
  В случае пустых списков функцию можно использовать как арифметическое сложение длин.
 *)
Fixpoint concat (a1 a2 : anum) : anum :=
  match a1 with
  | E => a2
  | L E => A E a2
  | L a1' => L (concat a1' a2)
  | A head1 tail1 => A head1 (concat tail1 a2)
  end.

From Coq Require Import Lia.

Lemma length_concat_correct : forall a1 a2, 
  get_size (concat a1 a2) = get_size a1 + get_size a2.
Proof. 
  induction a1; intros; simpl. 
  - reflexivity.
  - destruct a1;
    simpl; rewrite IHa1; auto with arith.
  - rewrite IHa1_2; auto with arith. 
Qed.


Fixpoint map_anet (f : anum -> anum) (a : anum) :=
  match a with
  | E => E
  | L _ => f a
  | A head tail => A (f head) (map_anet f tail)
  end.

Fixpoint anet_pairs (a1 a2 : anum) : anum :=
  match a1 with
  | E => E
  | L _ => map_anet (fun x => A a1 x) a2
  | A head1 tail1 => A (anet_pairs head1 a2) (anet_pairs tail1 a2)
  end.


(* Создаем некоторые списки для тестирования *)
Definition zero_dim_0  := init_anet0 0.
Definition three_dim_0 := init_anet0 3.
Definition three_dim_1 := init_anet1 3.
Definition three_dim_2 := init_anet2 3.
Definition custom_list := init_anet_with 3 three_dim_2.

(* Тесты для функции get_dim *)
Compute get_dim zero_dim_0.     (* Результат должен быть: 0 *)
Compute get_dim three_dim_0.    (* Результат должен быть: 0 *)
Compute get_dim three_dim_1.    (* Результат должен быть: 1 *)
Compute get_dim three_dim_2.    (* Результат должен быть: 2 *)
Compute get_dim custom_list.    (* Результат должен быть: 3 *)

(* Тесты для функции get_size *)
Compute get_size zero_dim_0.  (* Результат должен быть: 0 *)
Compute get_size three_dim_0. (* Результат должен быть: 3 (потому что список имеет 3 элемента) *)
Compute get_size three_dim_1. (* Результат должен быть: 3 (потому что список имеет 3 элемента) *)
Compute get_size three_dim_2. (* Результат должен быть: 3 (потому что список имеет 3 элемента) *)
Compute get_size custom_list. (* Результат должен быть: 3 *)

(* Создаём списки для тестирования *)
Definition list1 := (A (L E) (A (L E) E)).
Definition list2 := (A (L (L E)) (A (L (L E)) E)).

Definition nat_0 := init_anet0 0.
Definition nat_1 := init_anet0 1.
Definition nat_123 := init_anet0 123.
Definition nat_277 := init_anet0 277.

(* Запускаем тесты *)
Compute (concat list1 list2).
Compute get_size (concat nat_0 nat_277).
Compute get_size (concat nat_1 nat_277).
Compute get_size (concat nat_123 nat_0).
Compute get_size (concat nat_123 nat_1).
Compute get_size (concat nat_123 nat_277).

```

## Заключение

