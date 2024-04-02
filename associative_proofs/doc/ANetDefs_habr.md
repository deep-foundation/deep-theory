### Определения ассоциативных сетей

[Ссылка на исходник](https://github.com/deep-foundation/deep-theory/blob/main/associative_proofs/coq/ANetDefs.v)

```coq

Require Import PeanoNat.
Require Import Coq.Init.Nat.
Require Import Vector.
Require Import List.
Require Import Coq.Init.Datatypes.
Import ListNotations.
Import VectorNotations.

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

### Функции преобразования ассоциативных сетей

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
```

### Предикаты эквивалентности ассоциативных сетей

```coq
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

(* Предикат эквивалентности для ассоциативных сетей дуплетов ANetDf *)
Definition ANetDf_equiv (anet1: ANetDf) (anet2: ANetDf) : Prop := forall id, anet1 id = anet2 id.

(* Предикат эквивалентности для ассоциативных сетей дуплетов ANetDl *)
Definition ANetDl_equiv (anet1: ANetDl) (anet2: ANetDl) : Prop := anet1 = anet2.
```

### Леммы эквивалентности ассоциативных сетей

```coq
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
```

### Примеры преобразования ассоциативных сетей друг в друга

```coq
(*  Нотация записи списков  *)
Notation "{ }" := (nil) (at level 0).
Notation "{ x , .. , y }" := (cons x .. (cons y nil) ..) (at level 0).

(*  Трёхмерная асеть  *)
Definition complexExampleNet : ANetVf 3 :=
  fun id => match id with
  | 0 => [0; 0; 0]
  | 1 => [1; 1; 2]
  | 2 => [2; 4; 0]
  | 3 => [3; 0; 5]
  | 4 => [4; 1; 1]
  | S _ => [0; 0; 0]
  end.

(*  Вектора ссылок  *)
Definition exampleTuple0 : Vn 0 := [].
Definition exampleTuple1 : Vn 1 := [0].
Definition exampleTuple4 : Vn 4 := [3; 2; 1; 0].

(*  Преобразование векторов ссылок во вложенные упорядоченные пары (списки)  *)
Definition nestedPair0 := VnToNP exampleTuple0.
Definition nestedPair1 := VnToNP exampleTuple1.
Definition nestedPair4 := VnToNP exampleTuple4.

Compute nestedPair0.  (* Ожидается результат: { } *)
Compute nestedPair1.  (* Ожидается результат: {0} *)
Compute nestedPair4.  (* Ожидается результат: {3, 2, 1, 0} *)

(*  Вычисление значений преобразованной функции трёхмерной асети   *)
Compute (ANetVfToANetLf complexExampleNet) 0. (* Ожидается результат: {0, 0, 0} *)
Compute (ANetVfToANetLf complexExampleNet) 1. (* Ожидается результат: {1, 1, 2} *)
Compute (ANetVfToANetLf complexExampleNet) 2. (* Ожидается результат: {2, 4, 0} *)
Compute (ANetVfToANetLf complexExampleNet) 3. (* Ожидается результат: {3, 0, 5} *)
Compute (ANetVfToANetLf complexExampleNet) 4. (* Ожидается результат: {4, 1, 1} *)
Compute (ANetVfToANetLf complexExampleNet) 5. (* Ожидается результат: {0, 0, 0} *)

(*  Асеть вложенных УП (упорядоченных пар)  *)
Definition testPairsNet : ANetLf :=
  fun id => match id with
  | 0 => {5, 0, 8}
  | 1 => {7, 1, 2}
  | 2 => {2, 4, 5}
  | 3 => {3, 1, 5}
  | 4 => {4, 2, 1}
  | S _ => {0, 0, 0}
  end.

(*  Преоразованная асеть вложенных УП в трёхмерную асеть (размерность должна совпадать) *)
Definition testTuplesNet : ANetVf 3 :=
  ANetLfToANetVf testPairsNet.

(*  Вычисление значений преобразованной функции асети вложенных УП   *)
Compute testTuplesNet 0.   (* Ожидается результат: [5; 0; 8] *)
Compute testTuplesNet 1.   (* Ожидается результат: [7; 1; 2] *)
Compute testTuplesNet 2.   (* Ожидается результат: [2; 4; 5] *)
Compute testTuplesNet 3.   (* Ожидается результат: [3; 1; 5] *)
Compute testTuplesNet 4.   (* Ожидается результат: [4; 2; 1] *)
Compute testTuplesNet 5.   (* Ожидается результат: [0; 0; 0] *)

(*  Преобразование вложенных УП в асеть дуплетов  *)
Compute NPToANetDl { 121, 21, 1343 }.
(* Должно вернуть: {(121, 1), (21, 2), (1343, 2)} *)

(*  Добавление вложенных УП в асеть дуплетов  *)
Compute AddNPToANetDl {(121, 1), (21, 2), (1343, 2)} {12, 23, 34}. 
(* Ожидается результат: {(121, 1), (21, 2), (1343, 2), (12, 4), (23, 5), (34, 5)} *)

(*  Преобразование асети дуплетов во вложенные УП  *)
Compute ANetDlToNP {(121, 1), (21, 2), (1343, 2)}. 
(* Ожидается результат: {121, 21, 1343} *)
  
Compute ANetDlToNP {(121, 1), (21, 2), (1343, 2), (12, 4), (23, 5), (34, 5)}. 
(* Ожидается результат: {121, 21, 1343} *)

(*  Чтение вложенных УП из асети дуплетов по индексу дуплета - начала вложенных УП  *)
Compute ANetDl_readNP {(121, 1), (21, 2), (1343, 2), (12, 4), (23, 5), (34, 5)} 0.
(* Ожидается результат: {121, 21, 1343} *)

Compute ANetDl_readNP {(121, 1), (21, 2), (1343, 2), (12, 4), (23, 5), (34, 5)} 3.
(* Ожидается результат: {12, 23, 34} *)


(*  Определяем асеть вложенных УП *)
Definition test_anetl := { {121, 21, 1343}, {12, 23}, {34}, {121, 21, 1343}, {12, 23}, {34} }.

(*  Преобразованная асеть вложенных УП в асеть дуплетов  *)
Definition test_anetd := ANetLlToANetDl test_anetl.

(*  Вычисление преобразованной асети вложенных УП в асеть дуплетов  *)
Compute test_anetd.
(* Ожидается результат:
 {(121, 1), (21, 2), (1343, 2),
  (12, 4), (23, 4),
  (34, 5),
  (121, 7), (21, 8), (1343, 8),
  (12, 10), (23, 10),
  (34, 11)} *)


(*  Вычисления преобразования асети вложенных УП в асеть дуплетов и обратно в test_anetl *) 
Compute ANetDlToANetLl test_anetd.
(* Ожидается результат:
  {{121, 21, 1343}, {12, 23}, {34}, {121, 21, 1343}, {12, 23}, {34}}  *)

(*  Вычисления смещения вложенных УП в асети дуплетов по их порядковому номеру  *)
Compute ANetDl_offsetNP test_anetd 0.   (* Ожидается результат: 0 *)
Compute ANetDl_offsetNP test_anetd 1.   (* Ожидается результат: 3 *)
Compute ANetDl_offsetNP test_anetd 2.   (* Ожидается результат: 5 *)
Compute ANetDl_offsetNP test_anetd 3.   (* Ожидается результат: 6 *)
Compute ANetDl_offsetNP test_anetd 4.   (* Ожидается результат: 9 *)
Compute ANetDl_offsetNP test_anetd 5.   (* Ожидается результат: 11 *)
Compute ANetDl_offsetNP test_anetd 6.   (* Ожидается результат: 12 *)
Compute ANetDl_offsetNP test_anetd 7.   (* Ожидается результат: 12 *)


(*  Определяем трёхмерную асеть как последователность векторов длины 3  *)
Definition test_anetv : ANetVl 3 :=
  { [0; 0; 0], [1; 1; 2], [2; 4; 0], [3; 0; 5], [4; 1; 1], [0; 0; 0] }.

(*  Преобразованная трёхмерная асеть в асеть дуплетов через асеть вложенных УП  *)
Definition test_anetdl : ANetDl := ANetVlToANetDl test_anetv.

(*  Вычисление трёхмерной асети преобразованной в асеть дуплетов через асеть вложенных УП  *)
Compute test_anetdl.
(* Ожидается результат:
{ (0, 1), (0, 2), (0, 2),
  (1, 4), (1, 5), (2, 5),
  (2, 7), (4, 8), (0, 8),
  (3, 10), (0, 11), (5, 11),
  (4, 13), (1, 14), (1, 14),
  (0, 16), (0, 17), (0, 17)}  *)

(*  Преобразованная трёхмерная асеть в асеть дуплетов через асеть вложенных УП и наоборот в трёхмерную асеть  *)
Definition result_TuplesNet : ANetVl 3 :=
  ANetLlToANetVl (ANetDlToANetLl test_anetdl).

(*  Итоговая проверка эквивалентности ассоциативных сетей   *)
Compute result_TuplesNet.
(* Ожидается результат:
  { [0; 0; 0], [1; 1; 2], [2; 4; 0], [3; 0; 5], [4; 1; 1], [0; 0; 0] }  *)
```
