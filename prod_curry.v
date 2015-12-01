Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).

Theorem uncurry_curry : forall(X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  unfold prod_curry, prod_uncurry.
  simpl.
  reflexivity.
Qed.

Theorem curry_uncurry : forall(X Y Z : Type)
  (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros.
  unfold prod_curry, prod_uncurry.
  destruct p as [a b].
  simpl.
  reflexivity.
Qed.
