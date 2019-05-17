(*begin hide*)
Require Import String. Open Scope string_scope.
Require Import Program.

From mathcomp Require Import ssreflect ssrnat ssrbool eqtype fintype.
Import ssreflect ssrnat ssrbool ssrfun eqtype fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Add LoadPath "./" as Top.
Require Import Top.CaseTactic.
Require Import Top.Syntax.
Require Import Top.Semantics.

Require Import Vector.
Require Import VectorEq.
Require Import ZArith.

(*end hide*)

Theorem Coincidence_IntExp : forall (E : Env) (ie : IntExp E) (σ σ' : Σ(E)),
    (forall (w : Var E), σ ! w = σ' ! w) -> ⟦ ie ⟧ᵢ σ = ⟦ ie ⟧ᵢ σ'.
Proof.
  ¿?. (* Hueco a completar *)
Qed.

Theorem Coincidence_Assert : forall (E : Env) (ae : Assert E) (σ σ' : Σ(E)),
    (forall (w : Var E), σ ! w = σ' ! w) -> ⟦ ae ⟧ₐ σ = ⟦ ae ⟧ₐ σ'.
Proof.
  ¿?. (* Hueco a completar *)
Qed.
