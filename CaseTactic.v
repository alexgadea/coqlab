
Require String. Open Scope string_scope.

(* Nos permite completar cualquier definición utilizando el "?" *)
Definition admit {T: Type} : T.  Admitted.

Notation "?" := admit (at level 1, no associativity).

(*
  Por ejemplo si no estamos seguros con que expresión/programa definir una
  función podemos completar parcialmente con "?".
*)

Definition Tests (n : nat) : nat :=
  match n with
  | O => S 0
  | S x => ? (* este caso todavía no lo tenemos definido *)
  end
.

(* Nos permite completar cualquier prueba utilizando el "¿?" *)
Lemma ProofHole {T: Type} : forall (x y : T), x = y. Admitted.

Tactic Notation "¿?" := intros; apply ProofHole.

(* 
   Al igual que el "?" la notación "¿?" nos permite completar una prueba sobre
   la igualdad de dos cosas.
*)

Lemma Proof_of_Z_eq_SZ : 0 = 1.
Proof.
  ¿?. (* Claramente esta prueba no la vamos a poder completar nunca. *)
Qed.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

(* Nos permite introducir nombres a las subpruebas para leer mejor. *)
Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
