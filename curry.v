(* https://www.youtube.com/watch?v=i2Q5GJhgsjA *)
(* https://www.youtube.com/watch?v=2SjM5f3GkV0 *)
(* http://math.andrej.com/2011/02/22/video-tutorials-for-the-coq-proof-assistant/ *)

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

(* Prove that curry (uncurry g) is extensionally equivalent to g. *)
Theorem the_other : forall g a b, curry (uncurry g) a b = g a b.
Proof.
  intros.
  unfold curry, uncurry.
  simpl.
  reflexivity.
Qed.

(* There exist bijections back and forth. *)
Definition isomorphic (X Y : Set) :=
  exists u : X -> Y,
    exists v : Y -> X,
      (forall x, v (u x) = x /\ (forall y, u (v y) = y)).

Axiom extensionality : forall (X Y : Set) (f g : X -> Y),
  (forall x, f x = g x) -> f = g.

(* When you see your goal is going to fall apart into several cases,
  `split` is usually the proper tactic. *)
Theorem problem : isomorphic (A * B -> C) (A -> B -> C).
Proof.
  exists curry.
  exists uncurry.
  split.
  apply extensionality.
  intros [a b].
  apply better.
  intro g.
  apply extensionality.
  intro a.
  apply extensionality.
  intro b.
  apply the_other.
Qed.
