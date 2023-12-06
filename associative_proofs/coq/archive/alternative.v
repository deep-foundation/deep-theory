(* https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=9399ec7e3b37f574abe76c77aa4bed88 *)

Require Import Coq.Lists.List.
Require Import ZArith.
Open Scope Z_scope.

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

Check tupleToNestedPair [].
Compute tupleToNestedPair [].

Check tupleToNestedPair [0].
Compute tupleToNestedPair [0].

Check tupleToNestedPair [0; 1].
Compute tupleToNestedPair [0; 1].

Check tupleToNestedPair [0; 1; 2].
Compute tupleToNestedPair [0; 1; 2].

Check tupleToNestedPair [0; 1; 2; 3].
Compute tupleToNestedPair [0; 1; 2; 3].
