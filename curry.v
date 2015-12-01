Parameters A B C : Set.

(* A function f : A * B -> C is equivalent to a function A -> (B -> C). *)
Definition curry   (f : A * B -> C) := fun a => fun b => f (a, b).
Definition uncurry (g : A -> B -> C) := fun p => g (fst p) (snd p).

Theorem attempt : forall f, uncurry (curry f) = f.
Proof.
  intros.
  unfold curry, uncurry.
