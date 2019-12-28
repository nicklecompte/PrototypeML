; Writing Hygienic Macros in Scheme with Syntax-Case
; R. Kent Dybvig
; Indiana University Computer Science Department
; Bloomington, IN 47405
; dyb@cs.indiana.edu
; Copyright c 1992 R. Kent Dybvig
; August 1992

; Transcribed Dec 2019 by
; Nick LeCompte, as an exercise,
; from https://www.cs.indiana.edu/~dyb/pubs/tr356.pdf

; Scheme macro syntax consists of
;   - a set of defining forms
;   - a set of forms for taking apart and putting together syntax
;   - and a set of primitives for manipulating and comparing identifiers.

;   The system is based on a representation of expressions as abstract objects
; that are different from the commonly used Scheme representations. Macro
; transformers take syntax objects as input and return expanded syntax objects
; as output. Embedded wihin each syntax object is sufficient information
; to determine the bindings of all identifiers contained within the object,
; along with an internal representation of the syntactic form itself.
;   Other implementation-dependent information may be contained within a syntax
; object: for example, the position of the expression in tthe original source
; code may be included for debugging purposes.

;;; Syntactic forms and primitives ;;;

;   New macros are defined to extend the set of syntactic forms available within
; a program or subprogram. All extended syntactic forms, also referred to as
; "macro calls", take the form:
;
;   (keyword . subform)
;
; where \emph{keyword} is an identifier that names a macro. The syntax of
; \emph{subform} is determined by the macro and can vary significantly.
;   Macros defined using these facilities are automatically \emph{hygenic}.
; If a macro transformer inserts a binding for an identifier (variable or
; keyword), the new binding will not capture other identifiers (even of the same
; name) introduced elsewhere. Macros defined using these facilities are also
; referentially transparent.
;   If a macro transformer inserts a free reference to an identifier, the
; reference refers to the binding that was visible where the transformer was
; specified, regardless of any local bindings that may surround the use of the
; macro. In order to maintain these two properties, bound identifiers introduced
; may be renamed to avoid potential conflicts.
;
;   It is sometimes desirable to insert identifiers into the output of a macro
; that behave as if they had been present in the original expression - to have
; been captured by existing bindings, or for inserted bindings to capture
; existing references. This can be done in a controlled, hygenic fashion.
;
;   New syntactic forms are defined by associating an identifier,
; or \emph{keyword}, with a transformation procedure, or \emph{transformer}. At
; a top level, syntactic definitions take the form of
;
; (define-syntax keyword transformer-expression)
;
; The \emph{transformer-expression} must be an expression that evaluates to a
; transformer. When the expander encounters an expression of the form
; (keyword . subform), the expression is passed to the associated transformer
; for processing. The scope of syntactic definitions can be limited by using one
;  of the lexical binding forms:
;
; (let-syntax ((keyword transformer-expression) ...)
;   body)
; (letrec-syntax ((keyword transformer-expression) ...)
;   body)
;
; In both forms the \emph{keyword} denotes new syntax in \emph{body};
; for letrec-syntax the binding scope also includes each
;\emph{transformer-expression}.
;
;   Lexical macro keyword bindings, ordinary lexical variable bindings, and
; pattern variable bindings can shadow each other, and any lexical binding
; shadows a top-level binding for the same identifier. Any define-syntax forms
; appearing within the definitions at the front of a lambda body (or other
; similar body) are treated as letrec-syntax bindings.
;
;   Macro transformers are procedures of one argument. The argument to a macro
; transformer is a \emph{syntax object}, which contains contextual information
; about an expression in addition to its structure. This contextual information
; enables the macro system to determine, for each identifier contained within
; the expression, to which binding the identifier refers. This information is
; required to maintain hygeine and referential transparency. This same
; information also allows macro transformers to compare identrifiers according
; to their intended use as free identifiers, bound identifiers, or data. Syntax
; objects may contain other syntactic information that is not of direct interest
; to the macro writer. For example: syntax objects can contain source
; annotations thhat allow the evaluator to correlate the final object code with
; the source code that prodcued it.
;
;   The ouput from a transformer itself may be a macro call or contain macro
; calls, in which case further expansion is performed until no macro calls
; remain.
;
;   Transformers decompose their input using syntax-case and rebuild their
; output using syntax. A syntax-case expression takes the following form:
;
;   (syntax-case input-expression (literal ...) clause ...)
;
; Each clause takes one of the following two forms:
;
;   (pattern output-expression)
;   (pattern fender output-expression)
;
; syntax-case first evaluates the input-expression, then attempts to match the
; resulting value with the pattern from the first clause. This value is usually
; a syntax object but it can be any Scheme list structure. If the value matches
; the pattern and there is no fender present, output-expression is evaluated and
; its value is returned as the value of the syntax-case expression. If the value
;  does not match the pattern, the next clause is checked, and so on.
;
;   Patterns consist of list structures, identifiers, and constants. Each
; identifier within a pattern is either a
;   - literal,
;   - pattern variable, or
;   - ..., a special identifier representing an ellipsis
;
; Any identifier other than ... is a literal if it appears in the list of
; literals (literal ...) in the syntax-case expression; otherwise it is a
; pattern variable. Literals serve as auxillary keywords, such as else in
; case/cond expressions. List structure within a pattern specifies basic
; structure required of the input, pattern variables describe arbitrary
; substructures, and literals and constants specify atomic pieces that must
; match exactly. Ellipses specify repeated occurennces of the subpatterns they
;follow.
;
;   An input F matches a pattern P iff:
;   - P is a pattern variable,
;   - P is a literal identifier and F is an identifier
; with the same binding
;   - P is a pattern list (P_1...P_n) and F is a list
; of n forms that match P_1 through P_n;
;   - P is an improper pattern list (P_1...P_n . P_{n+1}),
; and F is a list or improper list of n or more forms that match P_1 through
; P_n, and whose nth cdr matches P_{n+1}, or P is of the form (P_1...P_n,
; P_n+1 ellipsis) where ellipsis is the identifier ... and F is a proper list
; of at least n elements, the first n of which match P_1 through P_n and each
; remaining element of F matchhes P_{n+1} -P is a pattern datum annd F is equal
; to P under the equal? procedure
;
;   If the optional \emph{fender} argument is present, it serves as an
; additional constraint on acceptance of a clause. If the value of
; \emph{input-expression} matches the pattern for a given clause, the
; corresponding \emph{fender} is evaluated. If \emph{fender} evaluates to a true
;  value the clause is accepted; otherwise it is rejected as if the input had
; failed to match the patttern. Fenders are logically part of the matching
; process; i.e. they specify additional constraints.
;
;    Pattern variables contained within a clause's \emph{ppattern} are bound to
; the corresponding pieces of the input value within the clause's fender and
; output-epxression. Although pattern variable bindings created by syntax-case
; can shadow (and be shadowed by) lexical and macro keyword bindings, pattern
; variables can be referenced only within syntax expressions. Scheme syntax
; expressions have the following form:
;
;   (syntax template)
;
; A syntax form returns a Scheme object in much the same  way as quote or
; quasiquote, with two important differences: the values of pattern variables
; appearing within \emph{template} are inserted into \emph{template}, and
; contextual syntactic information contained within \emph{template} are
; retained. All list structure within \emph{template} remains ordinary list
; structure in the output, and all orther items (including identifiers) are
; inserted without further interpretation. Contextual information associated
; with tthe valuyes of inserted pattern variables and any nonlist items from the
; template is retained in the output.
;
;   Within a template, a subtemplate followed by an ellipsis expands into zero
; or more occurences of the subtemplate. The subtemplate must contain at least
; one pattern variable tthat was in a subpattern followed by an ellipsis in
; input. (Otherwiuse, the expander could not determine how many times the
; subform should be repeated in the output.) This generalizes to nested
; ellipses. There is one exception:
; the special template (... ...) epxands into ....
; This is used by macro-defining macros to introduce  ellipses into the defined
; macros.
;
;   A pattern variable tthat occurs in a syntax template is replaced by the
; subform that it matched in the syntax-case expression that established the
; pattern variable's binding. Pattern variables that occur in subpatterns
; followed by one or more ellipses may occur only in subtemplates that are
; followed by (at least) as many ellipses in a syntax template, in which they
; are replaced in the output by all subforms matched in the input.
;
;   It is an error for a transformer to return a "raw" symbol: all names
; returned by a transformer must be identifiers introduced by syntax
; expressions. In other words, if a transformer returns a symbol, the behavior
; is undefined.
;
;   The system provides three predicates for recognizing and comparing
; identifiers {here taken to mean a syntax object representing an identifier}:
;   - identifier?, which returns true iff its argument is an identifier
;   - bound-identifier=?, which takes in two identifiers and determines if they
; are equal based on their intended use as bound identifiers in the output of a
; macro.
;   - free-identifier=? is like bound-identifier=? but instead determines if
; they are equal based on intended use as free identifiers in outoput of a macro
;
;   When it is necessary to determine if a binding introduced for one identifier
; would bind references to another, the predicate bound-identifier=? is used.
; Two identifiers are bound-identifier=? only if both have the same name and
; both were present in the original program or both were introduced by the same
; macro application. The predicate bound-identifier=? can be used for detecting
; duplicate variable names in a binding construct, or for other preprocessing of
; a binding construct that requires detecting instances of the bound variable.
; When it is necessary to determine if two identifiers, inserted as free
; references, would both refer to the same binding, the predicate
; free-identifier=? is used. Literal identifiers appearing in syntax-case
; patterns (such as else in cond) are matched using free-identifier=?
;
; Two identifiers may be free-identifier=? if they are not bound-identifier=?
; but the converse is never true. In general, when two identifiers are
; introduced at different macro expansion steps but both would refer to the same
; binding if inserted as free references, they are free-identifier=? but not
; bound-identifier=?
;
; Sometimes it is necessary to compare towo identifiers that will be inserted as
; symbolic data in the output of a macro.