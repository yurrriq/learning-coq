Parameters A B C : Set.

(* A function f : A * B -> C is equivalent to a function A -> (B -> C). *)
Definition curry   (f : A * B -> C) := fun a => fun b => f (a, b).
Definition uncurry (g : A -> B -> C) := fun p => g (fst p) (snd p).

(* "extensional equality" *)
Theorem better : forall f a b, uncurry (curry f) (a, b) = f (a, b).
Proof.
  intros.
  unfold curry, uncurry.
  simpl.
  (* auto. *)
  reflexivity.
Qed.
