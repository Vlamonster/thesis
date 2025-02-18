From Coq Require Import Nat Bool String List. Import ListNotations.

(* Atoms are propositional symbols mapped to the naturals. *)
Definition Atom := nat.

(* Literals are either positive or negated variants of atoms. *)
Inductive Literal : Type :=
    | posLit (p: Atom)
    | negLit (p: Atom).

Definition negateLiteral (l: Literal) : Literal :=
    match l with
    | posLit p => negLit p
    | negLit p => posLit p
    end.

(* A clause is a disjunction of literals. *)
Definition Clause := list Literal.

(* A formula is a conjunction of clauses. *)
Definition Formula := list Clause.

Definition negateClause (c: Clause) : Formula :=
    map (fun (l: Literal) => [negateLiteral l]) c.

(* A partial assignment for atoms to true or false.
   Note that `d` indicates if the assignment was a decision. *)
Inductive PartialAssignment : Type :=
  | empty
  | record (p: Atom) (v d: bool) (m: PartialAssignment).

Definition setAtom (m: PartialAssignment) (p: Atom) (v d: bool) : PartialAssignment :=
    record p v d m.

Definition setLiteral (m: PartialAssignment) (l: Literal) (d: bool) : PartialAssignment :=
    match l with
    | posLit p => setAtom m p true d
    | negLit p => setAtom m p false d
    end.

Fixpoint evalAtom (m: PartialAssignment) (p: Atom) : option bool :=
    match m with
    | empty => None
    | record p' v' d' m' => if p =? p' then Some v' else evalAtom m' p'
    end.

Definition evalLiteral (m: PartialAssignment) (l: Literal) : option bool :=
    match l with
    | posLit p => evalAtom m p
    | negLit p => option_map negb (evalAtom m p)
    end.

(* An atom is defined if it is assigned true or false. *)
Definition DefinedAtom (m: PartialAssignment) (p: Atom) : Prop :=
    exists (v: bool), evalAtom m p = Some v.

(* A literal is defined if its atom is assigned true or false. *)
Definition DefinedLiteral (m: PartialAssignment) (l: Literal) : Prop :=
    exists (v: bool), evalLiteral m l = Some v.

(* A partial assignment is total if all atoms are assigned true or false.
   The number of atoms is given by `n`. *)
Definition Total (m: PartialAssignment) (n: nat) : Prop :=
    forall (p: nat), p <= n -> exists (v: bool), evalAtom m p = Some v.

(* Obviously, if all atoms are defined, then the partial assignment is total. *)
Lemma definedImplTotal :
    forall (m: PartialAssignment) (n: nat),
        (forall (i: nat), i <= n -> DefinedAtom m i) -> Total m n.
Proof. unfold DefinedAtom, Total. intros. apply H. assumption. Qed.

Fixpoint evalClause (m: PartialAssignment) (c: Clause) : option bool :=
    match c with
    | [] => Some false
    | l' :: c' =>
        match evalLiteral m l' with
        | Some true => Some true
        | Some false => evalClause m c'
        | None =>
            match evalClause m c' with
            | Some true => Some true
            | Some false => None
            | None => None
            end
        end
    end.

Fixpoint evalFormula (m: PartialAssignment) (f: Formula) : option bool :=
    match f with
    | [] => Some true
    | c' :: f' =>
        match evalClause m c' with
        | Some true => evalFormula m f'
        | Some false => Some false
        | None =>
            match evalFormula m f' with
            | Some true => None
            | Some false => Some false
            | None => None
            end
        end
    end.

Compute evalFormula (record 5 true true empty) [[negLit 5]].
Compute evalFormula (record 5 true true empty) [[posLit 5]].
Compute evalFormula (record 5 true true empty) [[postLit 6]].

Definition Model (m: PartialAssignment) (f: Formula) : Prop :=
    evalFormula m f = Some true.

Definition Satisfiable (f: Formula) : Prop :=
    exists (m: PartialAssignment), Model m f.

Definition Unsatisfiable (f: Formula) : Prop :=
    ~Satisfiable f.

Definition Entails (f f': Formula) : Prop :=
    forall (m: PartialAssignment), Model m f -> Model m f'.

Definition Equivalent (f f': Formula) : Prop :=
    Entails f f' /\ Entails f' f.

Inductive State : Type :=
    | fail
    | state (m: PartialAssignment) (f: Formula).

Fixpoint toFormula (m: PartialAssignment) : Formula :=
    match m with
    | empty => []
    | record p' v' d' m' =>
        if v' then [posLit p'] :: (toFormula m')
        else [negLit p'] :: (toFormula m')
    end.

Definition Conflicting (m: PartialAssignment) (c: Clause) : Prop :=
    Entails (toFormula m) (negateClause c).
