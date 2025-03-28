Require Import Coq.Lists.List.
(* 
  `anum` - это индуктивный тип для представления ассоциативного (относительного) числа или ачисла.
  Ачисла могут быть использованы для представления любых структур данных и вычислений,
  включая натуральные числа, списки, деревья, графы, реляционные данные и ассоциативные сети кортежей.

  Обратите внимание, что поведение и свойства `anum` будут зависеть от конкретных сценариев использования и интерпретации,
  которую вы присваиваете каждому из конструкторов `self`, `link`.
*)
Inductive anum : Type :=
  | self : anum  (* признак рекурсивного замыкания связи на себя*)
  | link : anum -> anum -> anum. (* связь двух anum *)

(* Функция преобразования из натуральных чисел в `anum` *)
Definition nat_to_anum : nat -> anum :=
  fix nat_to_anum n :=
    match n with
    | O => self                          (* 0 - это `self` *)
    | S m => link (nat_to_anum m) self  (* n = S(m) создает связь с m и с `self` *)
    end.

(* Функция преобразования из `anum` в натуральные числа *)
Fixpoint anum_to_nat (a : anum) : nat :=
  match a with
  | self => O                         (* `self` соответствует 0 *)
  | link a1 _ => S (anum_to_nat a1)  (* связь `link` увеличивает значение на 1 *)
  end.


(* Определяем ассоциативный корень из 4х связей разного вида самозамыкания *)
(* Натуральный абит 8. Сущность. Безначальная и бесконечноая связь *)
Definition E : anum := 
  link self self.

(* Натуральный абит 9. Объект. Безначальная связь *)
Definition O : anum := 
  link self E.

(* Натуральный абит 6. Субъект. Бесконечная связь *)
Definition S : anum := 
  link E self.

(* Натуральный абит 1. Отношение. Конечная связь *)
Definition R : anum := 
  link O S.


(* 
- Фрактальные списки или древовидные структуры: конструктор `L` принимает два значения типа `anum` и связывает их вместе,
  создавая вложенную структуру. Таким образом, `anum` может представлять древовидные структуры,
  где `L` используется для создания узлов ветвления дерева.

- Натуральные числа: список из B может быть эквивалентным последовательности вложенных конструкторов `B` в конструкции натуральных чисел в Coq.

- Фрактальные структуры: благодаря рекурсивной природе `anum`, он может представлять фрактальные структуры.
  Каждый узел, созданный с помощью `L`, может содержать другие значения `anum`,
  которые сами могут быть деревьями, созданными с помощью `L`. Таким образом,
  `anum` может представлять собой отношение самоподобия и вложенности, характерное для фракталов.

- В контексте графа, например, `L` мог бы быть использован для представления ребра между двумя вершинами.
*)


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





