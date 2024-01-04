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
  anetvⁿ : L → Vn отображает идентификатор l из множества L в вектор идентификаторов длины n,
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
Require Import PeanoNat.
Require Import Coq.Init.Nat.
Require Import Vector.
Require Import List.
Require Import Coq.Init.Datatypes.
Import ListNotations.
Import VectorNotations.


(* Последовательность идентификаторов векторов: L ⊆ ℕ₀ *)
Definition L := nat.

(* Дефолтное значение L: ноль *)
Definition LDefault : L := 0.

(* Множество векторов идентификаторов длины n ∈ ℕ₀: Vn ⊆ Lⁿ *)
Definition Vn (n : nat) := t L n.

(* Дефолтное значение Vn *)
Definition VnDefault (n : nat) : Vn n := Vector.const LDefault n.

(* Множество всех ассоциаций: A = L × Vn *)
Definition A (n : nat) := prod L (Vn n).

(* Ассоциативная сеть векторов длины n (или n-мерная асеть) из семейства функций {anetvⁿ : L → Vn} *)
Definition ANetVf (n : nat) := L -> Vn n.
Definition ANetVl (n : nat) := list (Vn n).

(* Вложенные упорядоченные пары *)
Definition NP := list L.

Notation "{ }" := (nil) (at level 0).
Notation "{ x , .. , y }" := (cons x .. (cons y nil) ..) (at level 0).

(* Ассоциативная сеть вложенных упорядоченных пар: anetl : L → NP *)
Definition ANetLf := L -> NP.
Definition ANetLl := list NP.

(* Дуплет *)
Definition D := prod L L.

(* Дефолтное значение D: пара из двух LDefault, используется для обозначения пустого дуплета *)
Definition DDefault : D := (LDefault, LDefault).

(* Ассоциативная сеть дуплетов (или двумерная асеть): anetd : L → L² *)
Definition ANetDf := L -> D.
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

(* Определение anets_equiv вводит предикат эквивалентности двух ассоциативных сетей векторов,
 anet1 и anet2 типа ANetVf, обе переменной длины n. 

  Данный предикат описывает свойство "эквивалентности" для таких сетей.
 Он утверждает, что anet1 и anet2 считаются "эквивалентными", если для каждого идентификатора id вектор,
 связанный с id в anet1, точно совпадает с вектором, связанным с тем же id в anet2.
*)
Definition ANetVf_equiv {n: nat} (anet1: ANetVf n) (anet2: ANetVf n) : Prop :=
  forall id, anet1 id = anet2 id.

(* Определение anets_equiv вводит предикат эквивалентности двух ассоциативных сетей векторов,
 anet1 и anet2 типа ANetVl, обе переменной длины n.
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
 так что вы можете свободно конвертировать между Vn и NP,
 если это требуется в вашей реализации или доказательствах.
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
Определим операцию отображения этой сети в ассоциативную сеть вложенных упорядоченных пар anetl : L → NP, где NP = {(∅,∅) | (l,np), l ∈ L, np ∈ NP}.
Затем определим обратное отображение из ассоциативной сети вложенных упорядоченных пар обратно в ассоциативную сеть векторов длины n.

  Теорема утверждает:

Для любой ассоциативной сети векторов длины n, anetvⁿ, применение операции преобразования в ассоциативную сеть вложенных упорядоченных пар
 и обратное преобразование обратно в ассоциативную сеть векторов длины n обеспечивает восстановление исходной сети anetvⁿ.
То есть, если мы преобразуем anetvⁿ в anetl и потом обратно в anetvⁿ, то мы получим исходную ассоциативную сеть векторов anetvⁿ. Иначе говоря:

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

(*
  Про ФБО (функциональное бинарное отношение) в ТМ (теории множеств):
  
1. ФА (функция агрегирования) - это правило или процедура, которая каждому конкретному элементу сопоставляет определённое множество,
 и таким образом ФА описывает состав множества.

2. БО (бинарное отношение) можно рассматривать как подмножество ПП (прямого произведения) двух множеств.
  Таким образом, УП (упорядоченные пары), составляющие это БО, являются элементами множества, описывающего данное отношение.

3. Сопоставление элемента к соответствующему множеству в рамках ФА можно представить в виде УП (элемент, множество).
  Таким образом, ФА, описывающая множество, может быть представлена как ФБО, где каждая УП уникально сопоставляет элемент и его агрегирующее множество.

Вывод 1: состав множества можно описать ФА, представленной в виде ФБО состоящего из УП типа (элемент, множество).

4. Если мы имеем несколько ФА, каждая из которых определяется своим ФБО,
  то один и тот же элемент может быть сопоставлен разным множествам в рамках разных ФА.

5. Исходя из предыдущих утверждений, УП (элемент, множество) может сама по себе рассматриваться как элемент в контексте ФА.
  Сама ФА, представляющая набор таких упорядоченных пар, может рассматриваться как множество.
  Таким образом, ФА можно описать и интерпретировать как специфическое множество в рамках ТМ.

6. Исходя из определения ФА как множества УП, каждое такое множество можно интерпретировать как ФА,
  где каждый элемент этого множества является УП (элемент, множество). Далее, каждая такая УП интерпретируется как элемент.
  Это утверждение отражает, что в контексте ТМ, функции и элементы можно интерпретировать в рамках друг друга.

Вывод 2: ФА так же может описывать множество ФА, как ФБО состоящее из УП типа (УП, ФА).

Вывод 3: Т.к. ФА так же может описывать множество ФА, как ФБО состоящее из УП типа (УП, ФА),
  то для описания одной ФА достаточно наличия хотя бы одной УП типа (УП, ФА),
  таким образом ФА может идентифицировать УП типа (УП, ФА).

Вывод 4: ФА может самоопределить себя одной УП

В контексте теории типов: 

1. "Множество" обычно рассматривается как "тип", потому что один тип описывает множество значений.

2. "Функциональное бинарное отношение" или ФБО аналогично "функциональному типу",
 который представляет собой тип, истолкованный как функция от одного типа значения к другому.

3. "Функция агрегирования", ФА, в контексте теории типов подразумевает функцию типизации,
 которая определяет тип для заданного значения, таким образом реализуя процесс типизации значений.


Таким образом, эти понятия из теории множеств и функций транслируются в терминологию и концепции теории типов.

1. В теории типов, универсальная функция агрегирования (ФА) может быть воспринята как специальный тип или множество,
 значения которого являются кортежами, где каждый кортеж состоит из элемента и его типа (в данном случае ФА).

2. Понятие функционального бинарного отношения (ФБО) применимо к теории типов,
 где оно может быть интерпретировано как функциональный тип. В этом смысле может быть построена иерархия ФБО,
  где УП типа (УП, ФА) ссылается на себя, тем самым идентифицируя ФА.

3. В теории типов, функциональная агрегация (ФА) может интерпретировать себя как экземпляр самого типа (ФА),
 формирование которого она контролирует. Это означает, что ФА может определиться как тип,
  который включает УП типа (УП, этот же тип).

4. Это дает представление о самоссылочности в контексте теории типов,
 где функция агрегирования наводит тип на самого себя, обеспечивая возможность замыкания,
  более известного как неподвижная точка комбинатора или "Y-комбинатор" для языка программирования.


Функция агрегирования (ФА), при рассмотрении её как множества упорядоченных пар,
  может описывать не только соответствие между элементами и множествами,
  но и между упорядоченными парами (которые являются элементами) и другими ФА,
  создавая тем самым функциональное бинарное отношение (ФБО) типа (УП, ФА).
  То есть, ФА может маппировать упорядоченные пары (которые сами являются элементами) на другие функции агрегирования.

  Стоит отметить, что такой подход повышает уровень абстракции,
  поскольку элементы теперь могут быть представлены не только конкретными значениями,
  но и упорядоченными парами, а их маппинги - другими функциями агрегирования.
  Это может быть полезно в более сложных математических или компьютерных моделях,
  где условия отображения могут быть сами функциями или зависеть от них.
  
  Если рассматривать функцию агрегирования (ФА) как множество упорядоченных пар,
  где каждая пара представляет соответствие между УП и другой ФА,
  то каждая отдельная ФА с помощью только одной УП может описывать или идентифицировать другую ФА.

  Этот вывод показывает подход, при котором ФА могут быть вложенными или рекурсивными по своей структуре,
  когда ФА могут описывать или включать другие ФА.
  Это обеспечивает большую гибкость и мощь для описания сложных структур данных или функциональных отношений.
  Это также подчеркивает рекурсивную природу множеств и функций в теории множеств,
  где объекты могут содержать и быть содержимыми другими объектами одного и того же типа.


  Вариант описания значений типов:

1. Допустим, что связи образуют списки экземпляров типов: первый компонент ссылается на значение типа (элемент множества),
  второй на хвост списка значений (элементов множеств)
  Данная новая связь может быть и новым значением типа, и хвостом списка.
  Таким образом новую связь можно отнести ко многим спискам как значение головы.
*)

(*  Требования к представлению вложенных УП и асетей дуплетов в виде списков (последовательностей):

1. Нумерация с нуля с головы списка
2. Указатель на следующую по порядку вложенную УП
3. Возможность добавления вложенной УП в конец списка УП
4. Возможность добавления списков в конец асети дулпетов
5. Произвольный доступ к асети дуплетов по идентификатору (порядковому номеру) дуплета
*)

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

Данное преобразование можно делать по разному: с сохранением исходных идентификаторов векторов
либо с переиндексацией. Переиндексацию можно не делать если написать дополнительную функцию для
асети дуплетов которая возвращает вложенную упорядоченную пару по её идентификатору.
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


(*
  Теперь всё готово для преобразования асети дуплетов anetd : L → L²
 в асеть вложенных упорядоченных пар anetl : L → NP

Данное преобразование будем делать с сохранением исходных идентификаторов векторов.
Переиндексацию можно не делать, потому что есть функция ANetDl_offsetNP для
асети дуплетов которая возвращает смещение вложенной УП по её идентификатору.
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









