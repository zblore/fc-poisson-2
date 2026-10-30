#!/usr/bin/env python3
"""Check that Challenge.lean states Formal Conjectures' Poisson conjecture, and nothing else.

Palomar's Comparator checks that Solution proves the statements of Challenge.lean, with the same
definitions. This script checks the other link: that Challenge.lean is Formal Conjectures' text.

The check is a whitelist, not a search. Challenge.lean must consist of exactly:

* an optional header comment, `module`, `public import Mathlib.*` lines and a module docstring;
* `@[expose] public section`;
* `namespace MvPolynomial`, Formal Conjectures' `variable` line and its `poissonBracket`
  definition (docstring included), `end MvPolynomial`;
* `namespace Arxiv.«math.0608009»`, `open MvPolynomial`, Formal Conjectures' `variable` line, its
  `IsPoissonEndomorphism` and `PoissonConjectureFor` definitions, `end Arxiv.«math.0608009»`;
* `namespace PoissonConjecture`, `open Arxiv.«math.0608009»`, the same `variable` line, Formal
  Conjectures' four theorem statements, in its order, each with an optional docstring and the
  body `by sorry`, and `end PoissonConjecture`. (Palomar rejects escaped name components such as
  `«math.0608009»` in theorem names; the definitions keep their names, so the statements are the
  same terms.)

Each piece is compared character for character with Formal Conjectures at FC_COMMIT, and any other
line (a `variable`, `universe`, `open`, `def`, `instance`, `set_option`, `notation`, `attribute`,
...) fails the check. Free-text comments may not contain `/-`, so nested comments cannot hide or
expose code. The script also checks, on the Formal Conjectures side, that nothing in the source
file's context (an `omit`, a second `variable`, a `universe`) changes the copied statements.

`Poisson2/Defs.lean` and `Poisson2/FormalTarget.lean` (which proves the statements under both
namespaces) are checked textually too, as a regression check; Comparator is what guarantees that
they agree with Challenge.lean.

Usage:
  check-fc-match.py [FC_CHECKOUT]   check; without an argument, download FC at FC_COMMIT
  check-fc-match.py --self-test [FC_CHECKOUT]
                                    check, then confirm that a list of altered Challenge files
                                    (changed universe, extra instance binder, shadowing
                                    definitions, nested comments, ...) all fail
"""
import re
import sys
import urllib.request
from pathlib import Path

FC_COMMIT = "a6bf2bb646fc1926130c24781a3b3cf23d0ef288"
BRACKET = "FormalConjecturesForMathlib/Algebra/MvPolynomial/PoissonBracket.lean"
CONJECTURE = "FormalConjectures/Arxiv/math.0608009/PoissonConjecture.lean"
NAMESPACE = "Arxiv.«math.0608009»"
# Palomar rejects escaped name components such as «math.0608009» in theorem names, so
# Challenge.lean states the theorems here, with Formal Conjectures' leaf names.
PALOMAR_NAMESPACE = "PoissonConjecture"
VAR_R = "variable {R σ : Type*} [CommRing R] [Fintype σ]"
VAR_K = "variable {K : Type*} [Field K] [CharZero K]"
THEOREMS = [
    "poisson_conjecture",
    "poisson_conjecture.variants.dimension_two",
    "poisson_conjecture.variants.dimension_three",
    "poisson_conjecture.variants.dimension_ge_two",
]

# A block comment's body: no `-/` (which would end it) and no `/-` (which would nest).
COMMENT_BODY = r"(?:(?!-/|/-).)*"


def fc_source(root, path):
    if root is not None:
        return (Path(root) / path).read_text(encoding="utf-8")
    url = f"https://raw.githubusercontent.com/google-deepmind/formal-conjectures/{FC_COMMIT}/{path}"
    with urllib.request.urlopen(url) as response:
        return response.read().decode("utf-8").replace("\r\n", "\n")


def definition_block(text, name):
    """The docstring and body of `def name`, up to the next blank line."""
    pattern = re.compile(
        r"(?:variable \(K\) in\n)?/--(?:(?!-/).)*-/\n(?:noncomputable )?def "
        + re.escape(name) + r"\b.*?(?=\n\n)",
        re.S,
    )
    found = pattern.findall(text)
    if len(found) != 1:
        raise SystemExit(f"error: expected one definition of {name}, found {len(found)}")
    return found[0]


def theorem_statement(text, name):
    """`theorem name ... :=`, without docstring, attributes or proof."""
    pattern = re.compile(r"theorem " + re.escape(name) + r"(?=[ \n]).*?:=", re.S)
    found = pattern.findall(text)
    if len(found) != 1:
        raise SystemExit(f"error: expected one theorem {name}, found {len(found)}")
    return found[0]


def strip_comments(text):
    """`text` with block comments (nested) and line comments replaced by spaces."""
    out, depth, i = [], 0, 0
    while i < len(text):
        two = text[i:i + 2]
        if two == "/-":
            depth, i = depth + 1, i + 2
            out.append("  ")
        elif two == "-/" and depth:
            depth, i = depth - 1, i + 2
            out.append("  ")
        elif two == "--" and not depth:
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        else:
            out.append(text[i] if not depth or text[i] == "\n" else " ")
            i += 1
    return "".join(out)


def check_fc_context(bracket, conjecture):
    """Check that nothing in Formal Conjectures' files changes the copied statements' context."""
    failures = []
    if f"namespace MvPolynomial\n\n{VAR_R}\n\n/--" not in bracket:
        failures.append("Formal Conjectures: poissonBracket no longer follows `namespace "
                        "MvPolynomial` and its `variable` line directly")
    code = strip_comments(conjecture)
    last = code.index("theorem " + THEOREMS[-1])
    context = re.findall(
        r"^(?:variable|universe|open|omit|include|section|namespace|end|set_option|local|scoped"
        r"|attribute|instance|notation|infix|prefix|postfix|macro|syntax|noncomputable section)"
        r"\b.*$",
        code[:last], re.M)
    context = [line.rstrip() for line in context]
    expected = [f"namespace {NAMESPACE}", "open MvPolynomial JacobianConjecture", VAR_K,
                "variable (K) in"]
    scoped = [line for line in context if line.startswith("omit ") and line.endswith(" in")]
    if [line for line in context if line not in scoped] != expected:
        failures.append(f"Formal Conjectures: the context before the statements changed: {context}")
    for name in THEOREMS:
        before = [line.strip() for line in code[:code.index(f"theorem {name}")].splitlines()
                  if line.strip()]
        if not re.fullmatch(r"@\[category [^\]]*\]", before[-1]) or before[-2].endswith(" in"):
            failures.append(f"Formal Conjectures: {name} has something other than a docstring "
                            "and a category attribute before it")
    return failures


def expected_paragraphs(bracket, conjecture):
    """Challenge.lean's body, paragraph by paragraph, as literal strings or regexes."""
    theorem = lambda name: re.compile(
        r"(?:/--" + COMMENT_BODY + r"-/\n)?"
        + re.escape(theorem_statement(conjecture, name)) + r" by\n  sorry", re.S)
    return [
        "namespace MvPolynomial",
        VAR_R,
        definition_block(bracket, "poissonBracket"),
        "end MvPolynomial",
        f"namespace {NAMESPACE}",
        "open MvPolynomial",
        VAR_K,
        definition_block(conjecture, "IsPoissonEndomorphism"),
        definition_block(conjecture, "PoissonConjectureFor"),
        f"end {NAMESPACE}",
        f"namespace {PALOMAR_NAMESPACE}",
        f"open {NAMESPACE}",
        VAR_K,
        *[theorem(name) for name in THEOREMS],
        f"end {PALOMAR_NAMESPACE}",
    ]


HEADER = re.compile(
    r"(?:/-" + COMMENT_BODY + r"-/\n)?"
    r"module\n\n"
    r"(?:public import Mathlib(?:\.[A-Za-z0-9_]+)+\n)+\n"
    r"/-!" + COMMENT_BODY + r"-/\n\n"
    r"@\[expose\] public section\n\n",
    re.S,
)


def check_challenge(challenge, expected):
    """Failures of Challenge.lean against the whitelist; empty if it passes."""
    header = HEADER.match(challenge)
    if header is None:
        return ["Challenge.lean: the header (comment, `module`, Mathlib imports, module docstring, "
                "`@[expose] public section`) is not in the expected form"]
    body = challenge[header.end():]
    if not body.endswith("\n") or body.endswith("\n\n"):
        return ["Challenge.lean: the file must end with one newline after the last `end`"]
    paragraphs = body[:-1].split("\n\n")
    if len(paragraphs) != len(expected):
        return [f"Challenge.lean: {len(paragraphs)} top-level paragraphs, expected "
                f"{len(expected)}"]
    failures = []
    for index, (actual, wanted) in enumerate(zip(paragraphs, expected), 1):
        ok = actual == wanted if isinstance(wanted, str) else wanted.fullmatch(actual)
        if not ok:
            first = actual.splitlines()[0] if actual else ""
            failures.append(f"Challenge.lean: paragraph {index} (`{first}`) is not Formal "
                            "Conjectures' text")
    return failures


def check_regression(defs, target, bracket, conjecture):
    """Textual checks of the proof's own copies; Comparator is the real check of these."""
    failures = []
    for label, text in [("Poisson2/Defs.lean", defs)]:
        for line in (VAR_R, VAR_K):
            if line not in text:
                failures.append(f"{label} lacks `{line}`")
        for source, name in [(bracket, "poissonBracket"), (conjecture, "IsPoissonEndomorphism"),
                             (conjecture, "PoissonConjectureFor")]:
            if definition_block(text, name) != definition_block(source, name):
                failures.append(f"{label}: definition {name} differs from Formal Conjectures")
    for name in THEOREMS:
        # Once under Formal Conjectures' namespace and once under PALOMAR_NAMESPACE.
        found = re.findall(r"theorem " + re.escape(name) + r"(?=[ \n]).*?:=", target, re.S)
        if len(found) != 2 or any(s != theorem_statement(conjecture, name) for s in found):
            failures.append(f"Poisson2/FormalTarget.lean: statements of {name} differ")
    return failures


def mutations(challenge):
    """Altered Challenge files that must all fail. Each is (description, text)."""
    ns = f"namespace {NAMESPACE}\n"
    first_theorem = "/-- **The Poisson conjecture is false.** -/"
    cases = [
        ("universe of K restricted", challenge.replace(VAR_K, VAR_K.replace("Type*", "Type"))),
        ("extra instance binder", challenge.replace(VAR_K + "\n", VAR_K + "\n\nvariable "
                                                    "[DecidableEq K]\n")),
        ("shadowing variable before the theorems", challenge.replace(
            first_theorem, "variable {K : Type 1} [Field K] [CharZero K]\n\n" + first_theorem)),
        ("local Function.Bijective", challenge.replace(
            ns, ns + "\ndef Function.Bijective {α β : Type*} (_ : α → β) : Prop := True\n")),
        ("duplicated Fintype binder", challenge.replace(VAR_R, VAR_R + " [Fintype σ]")),
        ("set_option before the theorems", challenge.replace(
            first_theorem, "set_option autoImplicit true\n\n" + first_theorem)),
        ("open Classical added", challenge.replace("open MvPolynomial\n",
                                                   "open MvPolynomial Classical\n")),
        ("changed hypothesis", challenge.replace("(hn : 2 ≤ n)", "(hn : 3 ≤ n)")),
        ("changed definition body", challenge.replace("Function.Bijective φ",
                                                      "Function.Injective φ")),
        ("nested comment in a theorem docstring", challenge.replace(
            first_theorem, "/-- **The Poisson conjecture is false.** /- -/")),
        ("code hidden after a module docstring", challenge.replace(
            "@[expose] public section", "instance : Inhabited Nat := ⟨1⟩\n\n"
                                        "@[expose] public section")),
        ("non-Mathlib import", challenge.replace("public import Mathlib.Algebra.MvPolynomial."
                                                 "PDeriv\n", "public import Mathlib.Algebra."
                                                 "MvPolynomial.PDeriv\npublic import Batteries\n")),
        ("proof other than sorry", challenge.replace("¬ PoissonConjectureFor K 3 := by\n  sorry",
                                                     "¬ PoissonConjectureFor K 3 := by\n  "
                                                     "exact sorry")),
        ("local definition before the theorems", challenge.replace(
            f"open {NAMESPACE}\n", f"open {NAMESPACE}\n\ndef PoissonConjectureFor (K : Type*) "
                                   "(n : ℕ) : Prop := True\n")),
        ("open Classical before the theorems", challenge.replace(
            f"open {NAMESPACE}\n", f"open {NAMESPACE} Classical\n")),
        ("theorems in another namespace", challenge.replace(
            f"namespace {PALOMAR_NAMESPACE}\n", f"namespace {PALOMAR_NAMESPACE}.Other\n")),
        ("theorem dropped", re.sub(r"\n\n/-- \*\*The Poisson conjecture is false in dimension "
                                   r"`3`.*?sorry", "", challenge, flags=re.S)),
    ]
    for description, text in cases:
        if text == challenge:
            raise SystemExit(f"error: self-test mutation `{description}` did not apply")
    return cases


def main():
    args = sys.argv[1:]
    self_test = "--self-test" in args
    args = [a for a in args if a != "--self-test"]
    root = args[0] if args else None
    source = f"checkout {root}" if root else f"GitHub at {FC_COMMIT}"
    bracket = fc_source(root, BRACKET)
    conjecture = fc_source(root, CONJECTURE)
    repo = Path(__file__).resolve().parent.parent
    challenge = (repo / "Challenge.lean").read_text(encoding="utf-8")
    defs = (repo / "Poisson2" / "Defs.lean").read_text(encoding="utf-8")
    target = (repo / "Poisson2" / "FormalTarget.lean").read_text(encoding="utf-8")
    expected = expected_paragraphs(bracket, conjecture)
    failures = (check_fc_context(bracket, conjecture) + check_challenge(challenge, expected)
                + check_regression(defs, target, bracket, conjecture))
    if failures:
        print("\n".join(failures), file=sys.stderr)
        raise SystemExit(1)
    print(f"OK: Challenge.lean is Formal Conjectures' three definitions and four statements, and "
          f"nothing else (Formal Conjectures from {source})")
    if self_test:
        passed = [d for d, text in mutations(challenge) if not check_challenge(text, expected)]
        if passed:
            print("self-test FAILED, these altered files passed: " + "; ".join(passed),
                  file=sys.stderr)
            raise SystemExit(1)
        print(f"OK: self-test, all {len(mutations(challenge))} altered Challenge files fail")


if __name__ == "__main__":
    main()
