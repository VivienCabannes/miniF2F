#!/usr/bin/env python3
"""Generate Lean proof attempts for MiniF2F problems."""

import os
import re
import glob

BASE = "/Users/vivc/code/download/minif2f_data"

def read_file(path):
    with open(path, 'r') as f:
        return f.read()

def write_file(path, content):
    with open(path, 'w') as f:
        f.write(content)

def get_theorem_body(content):
    """Extract the part after 'theorem' and before 'sorry'"""
    # Find the theorem signature
    match = re.search(r'(theorem\s+\w+.*?):=\s*by\s+sorry', content, re.DOTALL)
    if match:
        return match.group(1)
    return ""

def has_subst_hyps(content):
    """Check if theorem has simple substitution hypotheses like h₀ : x = 4"""
    return bool(re.search(r'h[₀₁₂₃₄₅₆₇₈₉]\s*:\s*\w+\s*=\s*[\d/\-]+\s*[)\]]', content))

def count_hyps(content):
    """Count how many hypotheses the theorem has"""
    return len(re.findall(r'\(h[₀₁₂₃₄₅₆₇₈₉]', content))

def get_hyp_names(content):
    """Get the names of hypotheses"""
    return re.findall(r'\((h[₀₁₂₃₄₅₆₇₈₉ₜ\w]*)\s*:', content)

def get_var_types(content):
    """Get variable types"""
    types = set()
    for m in re.finditer(r'\(\w+(?:\s+\w+)*\s*:\s*(\w+)', content):
        types.add(m.group(1))
    return types

def goal_is_conjunction(content):
    """Check if the goal is a conjunction (∧)"""
    # Get the part after the last : and before := by sorry
    match = re.search(r':\s*\n?\s*(.*?)\s*:=\s*by\s+sorry', content, re.DOTALL)
    if match:
        goal = match.group(1)
        return '∧' in goal
    return False

def goal_type(content):
    """Determine the type of the goal"""
    match = re.search(r':\s*\n?\s*(.*?)\s*:=\s*by\s+sorry', content, re.DOTALL)
    if match:
        return match.group(1).strip()
    return ""

def involves_finset(content):
    return 'Finset' in content or '∑' in content or '∏' in content

def involves_real(content):
    return 'ℝ' in content or 'Real' in content

def involves_sqrt(content):
    return 'Real.sqrt' in content or 'sqrt' in content

def involves_log(content):
    return 'Real.log' in content or 'logb' in content

def involves_trig(content):
    return any(x in content for x in ['Real.sin', 'Real.cos', 'Real.tan'])

def involves_complex(content):
    return 'ℂ' in content or 'Complex' in content

def involves_abs(content):
    return 'abs' in content or '‖' in content

def involves_nat(content):
    return 'ℕ' in content and 'ℝ' not in content and 'ℚ' not in content and 'ℂ' not in content and 'ℤ' not in content

def involves_int(content):
    return 'ℤ' in content and 'ℝ' not in content and 'ℚ' not in content and 'ℂ' not in content

def involves_rat(content):
    return 'ℚ' in content

def involves_div(content):
    return '∣' in content or 'dvd' in content.lower()

def involves_induction(name):
    return name.startswith('induction_')

def involves_prime(content):
    return 'Prime' in content or 'Nat.Prime' in content

def involves_gcd(content):
    return 'gcd' in content.lower()

def involves_mod(content):
    return '%' in content or 'mod' in content.lower()

def involves_pow(content):
    return '^' in content

def involves_irrational(content):
    return 'Irrational' in content

def involves_exists(content):
    goal = goal_type(content)
    return goal.startswith('∃') or 'Exists' in goal

def involves_forall(content):
    goal = goal_type(content)
    return goal.startswith('∀') or 'forall' in goal

def involves_iff(content):
    goal = goal_type(content)
    return '↔' in goal

def involves_neg(content):
    goal = goal_type(content)
    return goal.startswith('¬')

def involves_set_membership(content):
    return '∈ S' in content or 'S.card' in content

def involves_function(content):
    return '(f :' in content or '(f:' in content

def has_concrete_substs(content):
    """Check if we have concrete variable substitutions"""
    matches = re.findall(r'\(h[₀₁₂₃₄₅₆₇₈₉]\s*:\s*(\w+)\s*=\s*([\d\-/]+)\)', content)
    return matches

def get_subst_proof(content, name):
    """Generate a substitution-based proof"""
    substs = has_concrete_substs(content)
    if substs:
        hyp_names = [f"h{chr(0x2080+i)}" for i in range(len(substs))]
        # Try: subst all, then norm_num or omega
        subst_cmds = []
        for s in substs:
            subst_cmds.append(f"subst {s[0]}")
        return "\n  ".join(subst_cmds) + "\n  norm_num"
    return None

def generate_proof(filepath, content, name):
    """Generate a proof attempt for the given theorem."""
    goal = goal_type(content)
    hyps = get_hyp_names(content)

    # Category 1: Problems with direct variable substitutions (h₀ : x = 4)
    substs = has_concrete_substs(content)
    if substs and not involves_finset(content) and not involves_function(content):
        var_names = [s[0] for s in substs]
        # Build subst commands
        subst_lines = " ".join([f"subst h{chr(0x2080+i)}" for i in range(len(substs)) if f"h{chr(0x2080+i)}" in content])
        if subst_lines:
            if goal_is_conjunction(content):
                return f"{subst_lines}; constructor <;> norm_num"
            elif involves_mod(content) or involves_nat(content) or involves_int(content):
                return f"{subst_lines}; omega"
            else:
                return f"{subst_lines}; norm_num"

    # Category 2: Induction problems
    if involves_induction(name):
        if involves_div(content) and '(n : ℕ)' in content:
            return generate_induction_div_proof(content, name)
        elif '(n : ℕ)' in content:
            return generate_induction_proof(content, name)

    # Category 3: Pure natural number / integer arithmetic without complex structures
    if involves_nat(content) and not involves_finset(content) and not involves_function(content):
        if involves_div(content) and not involves_exists(content):
            if goal_is_conjunction(content):
                return "constructor <;> omega"
            return "omega"
        if involves_mod(content):
            return "omega"
        if goal_is_conjunction(content):
            return "constructor <;> omega"
        if involves_exists(content):
            return None  # Complex, handle case by case
        return "omega"

    if involves_int(content) and not involves_finset(content) and not involves_function(content) and not involves_real(content):
        if goal_is_conjunction(content):
            return "constructor <;> omega"
        if not involves_exists(content):
            return "omega"

    # Category 4: Simple real number arithmetic/algebra
    if involves_real(content) and not involves_sqrt(content) and not involves_log(content) and not involves_trig(content) and not involves_finset(content) and not involves_complex(content) and not involves_abs(content) and not involves_function(content):
        if goal_is_conjunction(content):
            hyp_list = ", ".join(hyps) if hyps else ""
            return f"obtain ⟨{', '.join([f'h{i}' for i in range(len(hyps))])}⟩ := sorry" if not hyps else f"constructor <;> nlinarith [{', '.join([f'{h}' for h in hyps])}]" if hyps else "constructor <;> norm_num"
        if '≤' in goal or '<' in goal or '≥' in goal or '>' in goal:
            if hyps:
                sq_hints = []
                # Add sq_nonneg hints for all variables
                vars_match = re.findall(r'\((\w+)\s+(?:\w+\s+)*:\s*ℝ\)', content)
                for v in vars_match:
                    sq_hints.append(f"sq_nonneg {v}")
                    sq_hints.append(f"sq_nonneg ({v})")
                hint_str = ", ".join([h for h in hyps] + sq_hints[:6])
                return f"nlinarith [{hint_str}]"
            return "nlinarith"
        if '=' in goal and '≠' not in goal:
            if hyps:
                return f"linarith [{', '.join(hyps)}]"
            return "norm_num"

    # Category 5: Number theory - GCD
    if involves_gcd(content):
        if involves_nat(content) or '(n : ℕ)' in content:
            if 'Nat.gcd' in content:
                return "rw [Nat.Coprime]; omega"
        return None

    # Category 6: Existence proofs
    if involves_exists(content) and not involves_finset(content):
        if 'Irrational' in content:
            return generate_irrational_proof(content, name)
        return None

    # Category 7: Finset computations
    if involves_finset(content):
        if '∑' in goal and 'Finset.range' in content:
            # Try native_decide or norm_num with simp
            return "simp [Finset.sum_range_succ]; norm_num"
        if '%' in goal or 'mod' in goal.lower():
            return "simp [Finset.sum_range_succ]; omega"
        return None

    # Category 8: Divisibility in ℤ
    if involves_div(content) and involves_int(content):
        return None

    # Default: try norm_num, then omega
    if not involves_real(content) and not involves_complex(content) and not involves_rat(content):
        return "omega"

    return None


def generate_induction_proof(content, name):
    """Generate induction proofs"""
    goal = goal_type(content)

    if '11 ∣' in content and '10^n' in content:
        return """induction n with
  | zero => simp
  | succ n ih =>
    have h : (10 : ℤ)^(n+1) = 10 * 10^n := by ring
    have h2 : (-1 : ℤ)^(n+1) = -1 * (-1)^n := by ring
    rw [h, h2]
    have : (10 * 10 ^ n - -1 * (-1) ^ n) = 11 * 10^n - (10^n - (-1)^n) := by ring
    rw [this]
    exact dvd_sub (dvd_mul_right 11 _) ih"""

    if '12 ∣ 4^(n+1) + 20' in goal:
        return """induction n with
  | zero => norm_num
  | succ n ih =>
    have : 4 ^ (n + 1 + 1) + 20 = 4 * (4 ^ (n + 1) + 20) - 60 := by ring
    omega"""

    if 'n!' in content or 'factorial' in content.lower():
        return None

    # Generic induction attempt
    if '∣' in goal:
        return None
    if '≤' in goal or '<' in goal:
        return None
    if '=' in goal:
        return None

    return None


def generate_induction_div_proof(content, name):
    """Generate induction proofs for divisibility"""
    return generate_induction_proof(content, name)


def generate_irrational_proof(content, name):
    """Generate proofs involving irrationals"""
    if 'exirrpowirrrat' in name:
        return """use Real.sqrt 2, Real.sqrt 2
  refine ⟨irrational_sqrt_two, irrational_sqrt_two, ?_⟩
  rw [show Real.sqrt 2 ^ Real.sqrt 2 = Real.sqrt 2 ^ Real.sqrt 2 from rfl]
  sorry"""
    return None


def process_file(filepath):
    """Process a single file and generate a proof attempt."""
    content = read_file(filepath)

    # Extract theorem name
    match = re.search(r'theorem\s+(\w+)', content)
    if not match:
        return None
    name = match.group(1)

    proof = generate_proof(filepath, content, name)
    if proof:
        new_content = content.replace('by sorry', f'by\n  {proof}')
        return new_content
    return None


def main():
    files = sorted(glob.glob(os.path.join(BASE, "test", "*", "ground_truth.lean")) +
                   glob.glob(os.path.join(BASE, "valid", "*", "ground_truth.lean")))

    solved = 0
    skipped = 0
    total = len(files)

    for filepath in files:
        content = read_file(filepath)
        match = re.search(r'theorem\s+(\w+)', content)
        name = match.group(1) if match else "unknown"

        result = process_file(filepath)
        if result:
            write_file(filepath, result)
            solved += 1
            print(f"[PROOF] {name}")
        else:
            skipped += 1
            print(f"[SKIP]  {name}")

    print(f"\nTotal: {total}, Attempted: {solved}, Skipped: {skipped}")


if __name__ == "__main__":
    main()
