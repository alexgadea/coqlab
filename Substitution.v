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
Require Import Top.Coincidence.

Require Import Vector.
Require Import VectorEq.
Require Import ZArith.
(*end hide*)

Theorem Substitution_IntExp :
  forall (E E' : Env) (ie : IntExp E) (σ : Σ(E')) (σ' : Σ(E)) (δ : Δ E E'),
    (forall (w : Var E), ⟦ δ w ⟧ᵢ σ  = σ' ! w) -> ⟦ ie ⫽ᵢ δ ⟧ᵢ σ = ⟦ ie ⟧ᵢ σ'.
Proof.
  ¿?. (* Hueco a completar *)
Qed.

Theorem Substitution_BoolExp :
  forall (E : Env) (ae : Assert E) (E' : Env) (σ : Σ(E')) (σ' : Σ(E)) (δ : Δ E E') ,
    (forall (w : Var E), ⟦ δ w ⟧ᵢ σ  = σ' ! w) -> ⟦ ae ⫽ₐ δ ⟧ₐ σ = ⟦ ae ⟧ₐ σ'.
Proof.
  ¿?. (* Hueco a completar *)
Qed.
