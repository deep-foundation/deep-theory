Require Import Coq.Lists.List.
Require Import ZArith.

Import ListNotations Z.

Inductive NestedPair : Type :=
  | Empty : NestedPair
  | Singlet : Z -> NestedPair
  | Doublet : Z -> NestedPair -> NestedPair.

Fixpoint tupleToNestedPair (l : list Z) : NestedPair :=
  match l with
  | [] => Empty
  | [a] => Singlet a
  | a :: l' => Doublet a (tupleToNestedPair l')
  end.