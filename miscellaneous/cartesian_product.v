Require Import List.

(* Cartesian product of two lists as a list of pairs *)
Definition cartesian_product {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  flat_map (fun a => map (fun b => (a, b)) l2) l1.

(* Cartesian product for scalar values, wrapped in lists *)
Definition cartesian_product_scalar {A B : Type} (a: A) (b: B) : list (A * B) :=
  cartesian_product (cons a nil) (cons b nil).

(* Example usage with scalar values *)
Example scalar_example: cartesian_product_scalar 2 3 = cons (2, 3) nil.
Proof.
  reflexivity.
Qed.

(* Example usage with vector (lists) *)
Example vector_example: cartesian_product (cons 1 (cons 2 nil)) (cons 1 (cons 2 nil)) =
                        cons (1, 1) (cons (1, 2) (cons (2, 1) (cons (2, 2) nil))).
Proof.
  reflexivity.
Qed.

(* Extracting the Python code example *)
Extraction "cartesian_product.py" cartesian_product cartesian_product_scalar.