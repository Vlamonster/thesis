From Coq Require Import Nat Bool String List. Import ListNotations.

(* Atoms are propositional symbols mapped to the naturals. *)
Definition Atom := nat.

(* Literals are either positive or negated variants of atoms. *)
Inductive Literal : Type :=
    | posLit (p: Atom)
    | negLit (p: Atom).

Notation "+ p" := (posLit p) (at level 35, right associativity).
Notation "- p" := (negLit p) (at level 35, right associativity).

Definition negateLiteral (l: Literal) : Literal :=
    match l with
    | +p => -p
    | -p => +p
    end.

Notation "~ l" := (negateLiteral l) (at level 75, right associativity).

(* A clause is a disjunction of literals. *)
Definition Clause := list Literal.

(* A formula is a conjunction of clauses. *)
Definition Formula := list Clause.

(* The antecedent is the reason for the value of a set literal. *)
Inductive Antecedent : Type :=
    | decided
    | propagated.

Definition negateClause (c: Clause) : Formula :=
    map (fun (l: Literal) => [~l]) c.

(* A partial assignment for atoms to true or false. *)
Inductive PartialAssignment : Type :=
    | empty
    | record (p: Atom) (v: bool) (a: Antecedent) (m: PartialAssignment).

Fixpoint appendPartialAssignment (m n: PartialAssignment) : PartialAssignment :=
    match n with
    | empty => m
    | record p' v' a' n' =>  record p' v' a' (appendPartialAssignment m n')
    end.

Notation "m ++a n" := (appendPartialAssignment m n) (at level 65, left associativity).

Definition setAtom (m: PartialAssignment) (p: Atom) (v: bool) (a: Antecedent): PartialAssignment :=
    record p v a m.

Definition setLiteral (m: PartialAssignment) (l: Literal) (a: Antecedent) : PartialAssignment :=
    match l with
    | +p => setAtom m p true a
    | -p => setAtom m p false a
    end.

Definition decideLiteral (m: PartialAssignment) (l: Literal) : PartialAssignment :=
    setLiteral m l decided.

Notation "m ++d l" := (decideLiteral m l) (at level 65, left associativity).

Definition propagateLiteral (m: PartialAssignment) (l: Literal) : PartialAssignment :=
    setLiteral m l propagated.

Notation "m ++p l" := (propagateLiteral m l) (at level 65, left associativity).

Fixpoint antecedentAtom (m: PartialAssignment) (p: Atom) : option Antecedent :=
    match m with
    | empty => None
    | record p' v' a' m' => if p =? p' then Some a' else antecedentAtom m' p'
    end.

Definition antecedentLiteral (m: PartialAssignment) (l: Literal) : option Antecedent :=
    match l with
    | +p => antecedentAtom m p
    | -p => antecedentAtom m p
    end.

Fixpoint evalAtom (m: PartialAssignment) (p: Atom) : option bool :=
    match m with
    | empty => None
    | record p' v' a' m' => if p =? p' then Some v' else evalAtom m' p
    end.

Definition evalLiteral (m: PartialAssignment) (l: Literal) : option bool :=
    match l with
    | +p => evalAtom m p
    | -p => option_map negb (evalAtom m p)
    end.

(* An atom is defined if it is assigned true or false. *)
Definition DefinedAtom (m: PartialAssignment) (p: Atom) : Prop :=
    exists (v: bool), evalAtom m p = Some v.

Definition UndefinedAtom (m: PartialAssignment) (p: Atom) : Prop :=
    ~DefinedAtom m p.

(* A literal is defined if its atom is assigned true or false. *)
Definition DefinedLiteral (m: PartialAssignment) (l: Literal) : Prop :=
    exists (v: bool), evalLiteral m l = Some v.

Definition UndefinedLiteral (m: PartialAssignment) (l: Literal) : Prop :=
    ~DefinedLiteral m l.

Definition NoDecisionLiterals (m: PartialAssignment) : Prop :=
  forall (l: Literal), DefinedLiteral m l -> antecedentLiteral m l = Some propagated.

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

Compute evalFormula (empty ++d +5) [[-(5)]]. (* Some false *)
Compute evalFormula (empty ++d +5) [[+5]].   (* Some true *)
Compute evalFormula (empty ++d +5) [[+6]].   (* None *)

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
    | failState (depth: nat)
    | state (depth: nat) (m: PartialAssignment) (f: Formula).

Fixpoint toFormula (m: PartialAssignment) : Formula :=
    match m with
    | empty => []
    | record p' v' d' m' =>
        if v' then (toFormula m') ++ [[+p']]
        else (toFormula m') ++ [[-p']]
    end.

Definition Conflicting (m: PartialAssignment) (c: Clause) : Prop :=
    Entails (toFormula m) (negateClause c).

Inductive Derived : State -> Prop :=
    (* If a clause is false except for one unassigned literal, assign it to satisfy the clause. *)
    | unitPropagate (d: nat) (m: PartialAssignment) (f: Formula) (l: Literal) (c: Clause) :
        (* The literal is in the clause. *)
        In l c ->
        (* The clause is in the formula. *)
        In c f ->
        (* There is at least one non-false literal in the clause.  *)
        evalClause m c = None ->
        (* The literal must be an unassigned literal. *)
        evalClause (m ++d ~l) c = Some false ->
        Derived (state d m f) ->
        Derived (state (S d) (m ++p l) f)

    (* If a literal appears only positively in f, it must be true. *)
    | pureLiteral (d: nat) (m: PartialAssignment) (f: Formula) (l: Literal) (c: Clause) :
        (* The literal is in the clause. *)
        In l c ->
        (* The clause is in the formula. *)
        In c f ->
        (* The literal is not defined yet. *)
        UndefinedLiteral m l ->
        (* The negation of the literal appears nowhere in no clause of the formula. *)
        ~(exists (c': Clause), In (~l) c' /\ In c' f) ->
        Derived (state d m f) ->
        Derived (state (S d) (m ++p l) f)

    (* Arbitrarily set an unassigned literal to true. *)
    | decide (d: nat) (m: PartialAssignment) (f: Formula) (l: Literal) (c: Clause) :
        (* The literal is in the clause. *)
        In l c ->
        (* The clause is in the formula. *)
        In c f ->
        (* The literal is not defined yet. *)
        UndefinedLiteral m l ->
        Derived (state d m f) ->
        Derived (state (S d) (m ++d l) f)

    (* Fail if all literals are assigned and there is a conflict. *)
    | fail (d: nat) (m: PartialAssignment) (f: Formula) (c: Clause) :
        (* The clause is in the formula. *)
        In c f ->
        (* The partial assignment is conflicting with the clause. *)
        Conflicting m c ->
        (* There are no decision literals to backtrack to. *)
        NoDecisionLiterals m ->
        Derived (state d m f) ->
        Derived (failState (S d))

    (* Backtrack by flipping the most recent decision literal. *)
    | backtrack (d: nat) (m n: PartialAssignment) (f: Formula) (l: Literal) (c: Clause) :
        let mln := m ++d l ++a n in
        (* The clause is in the formula. *)
        In c f ->
        (* The partial assignment is conflicting with the clause. *)
        Conflicting mln c ->
        (* There are no decision literals to backtrack to in n. *)
        NoDecisionLiterals n ->
        (* The literal l is the most recent decision literal to backtrack to. *)
        antecedentLiteral mln l = Some decided ->
        Derived (state d mln f) ->
        Derived (state (S d) (m ++d ~l) f).

Definition singleClause : Formula := [[+1; +2; +3]].
Definition firstTwoFalse : PartialAssignment := empty ++d -(1) ++d -(2).
Example unitPropagationSingleClause :
    Derived (state 0 firstTwoFalse singleClause) ->
    Derived (state 1 (firstTwoFalse ++p +3) singleClause).
Proof.
    apply unitPropagate with [+1; +2; +3].
    - simpl. right. right. left. reflexivity.
    - simpl. left. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Definition twoClauses : Formula := [[+1; +2];[+1; +3]].
Example pureLiteralTwoClauses :
    Derived (state 0 empty twoClauses) ->
    Derived (state 1 (empty ++p +1) twoClauses).
Proof.
    apply pureLiteral with [+1; +2].
    - simpl. left. reflexivity.
    - simpl. left. reflexivity.
    - unfold UndefinedLiteral. unfold DefinedLiteral, not. simpl. intros. destruct H as [v H]. discriminate H.
    - unfold not. simpl. intros. destruct H as [c [H [G1|[G2|G3]]]].
        * rewrite <- G1 in H. simpl in H. destruct H as [H1|[H2|H3]].
            + discriminate.
            + discriminate.
            + contradiction.
        * rewrite <- G2 in H. simpl in H. destruct H as [H1|[H2|H3]].
            + discriminate.
            + discriminate.
            + contradiction.
        * contradiction.
Qed.

Example decideSingleClause :
    Derived (state 0 empty singleClause) ->
    Derived (state 1 (empty ++d +1) singleClause).
Proof.
    apply decide with [+1; +2; +3].
    - simpl. left. reflexivity.
    - simpl. left. reflexivity.
    - unfold UndefinedLiteral. unfold DefinedLiteral, not. simpl. intros. destruct H as [v H]. discriminate.
Qed.

Definition allThreeFalse : PartialAssignment := firstTwoFalse ++d -(3).
Example backtrackSingleClause :
    Derived (state 0 allThreeFalse singleClause) ->
    Derived (state 1 (firstTwoFalse ++d +3) singleClause).
Proof.
    apply backtrack with (m := firstTwoFalse) (l := -(3)) (n := empty) (c := [+1; +2; +3]).
    - simpl. left. reflexivity.
    - unfold Conflicting. unfold Entails. simpl. intros. assumption.
    - unfold NoDecisionLiterals. unfold DefinedLiteral. intros. destruct H as [v H]. destruct l; simpl in H; discriminate.
    - simpl. reflexivity.
Qed.
