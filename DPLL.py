import re
import os
import random
import copy
import datetime

class DPLL:
    def __init__(self, formula):
        self.formula = formula
        self.atomic_props = self.get_atomic_props(formula)
    
    def get_atomic_props(self, formula):
        atomic_props = set()
        for clause in formula:
            for lit in clause:
                atomic_props.add(abs(lit))
        return list(atomic_props)
    
    def add_to_assignments(self, assignments, lits):
        copied_assignments = copy.deepcopy(assignments)
        for lit in lits:
            copied_assignments[abs(lit)] = 1 if lit > 0 else 0
        return copied_assignments

    def get_lit_counts(self, formula):
        ap_counts = {}
        for clause in formula:
            for ap in clause:
                ap_counts[ap] = 0 if ap not in ap_counts else ap_counts[ap]
                ap_counts[ap] += 1
        return ap_counts
    
    def get_unit_lits(self, formula):
        return [clause[0] for clause in formula if len(clause) == 1]

    def get_pure_lits(self, formula):
        lit_counts = self.get_lit_counts(formula)
        pure_lits = [lit for lit, _ in lit_counts.items() if -lit not in lit_counts]
        return pure_lits

    def heuristic_random(self, formula, assignments):
        assigned_vars = assignments.keys()
        unassigned_vars = [var for var in self.atomic_props if var not in assigned_vars]
        return [random.choice(unassigned_vars)]

    def compute_val(self, lit, assignments):
        if abs(lit) not in assignments:
            return -1
        elif assignments[abs(lit)][0] == 1:
            if lit > 0:
                return 1
            else:
                return 0

        if lit < 0:
            return 1
        else:
            return 0

    def shorten_formula(self, formula, assignment):
        shortened_formula = []
        for clause in formula:
            shortened_clause = []
            satisfied_clause = False
            for lit in clause:
                if self.compute_val(lit, assignment) == 1:
                    satisfied_clause = True
                    break
                if self.compute_val(lit, assignment) == -1:
                    shortened_clause.append(lit)
            if not satisfied_clause:
                shortened_formula.append(shortened_clause)
        return shortened_formula

    def assign_next_var(self, formula, assignments, shortened=False):
        if shortened:
            formula = self.shorten_formula(formula, assignments)
        if len(formula) == 0:
            next_var = 0
        else:
            next_var = self.heuristic_random(formula, assignments)[0]
        if next_var == 0:
            next_var_val = -1
        else:
            next_var_val = 1
        return next_var, next_var_val

    def resolve_by_lit(self, formula, lit):
        resolved_formula = []
        for clause in formula:
            if -lit in clause:
                resolved_clause = [literal for literal in clause if literal != -lit]
                if len(resolved_clause) == 0:
                    return resolved_formula, [lit], True
                resolved_formula.append(resolved_clause)
            elif lit not in clause:
                resolved_formula.append(clause)
        return resolved_formula, [lit], False 

    def resolve_by_pure_aps(self, formula):
        pure_aps = self.get_pure_lits(formula)
        for pure_ap in pure_aps:
            formula, _, unsat = self.resolve_by_lit(formula, pure_ap)
        return formula, pure_aps, False

    def resolve_by_unit_propagation(self, formula):
        assignments = []
        single_ap_clauses = self.get_unit_lits(formula)
        while len(single_ap_clauses) > 0:
            ap = single_ap_clauses[0]
            formula, _, unsat = self.resolve_by_lit(formula, ap)
            if unsat:
                return formula, [], True
            if not formula:
                assignments.append(ap)
                return formula, assignments, False
            assignments.append(ap)
            single_ap_clauses = self.get_unit_lits(formula)
        return formula, assignments, False

    def _solve(self, level, formula, assignments={}):
        formula, pure_aps, unsat = self.resolve_by_pure_aps(formula)
        assignments = self.add_to_assignments(assignments, pure_aps)
        formula, new_assignments, unsat = self.resolve_by_unit_propagation(formula)
        assignments = self.add_to_assignments(assignments, new_assignments)
        if unsat:
            return formula, assignments, True
        if not formula:
            return formula, assignments, False
        next_ap, next_var_val = self.assign_next_var(formula, assignments)
        next_lit = next_ap if next_var_val == 1 else -next_ap
        tmp_formula, tmp_assignments, unsat = self.resolve_by_lit(formula, next_lit)
        tmp_formula, tmp_assignments, unsat = self._solve(level+1, tmp_formula, self.add_to_assignments(assignments, [next_lit]))
        if unsat:
            tmp_formula, tmp_assignments, unsat = self.resolve_by_lit(formula, -next_lit)
            tmp_formula, tmp_assignments, unsat = self._solve(level+1, tmp_formula, self.add_to_assignments(assignments, [-next_lit]))
        return tmp_formula, tmp_assignments, unsat

    def solve_sat(self):
        assignments = {}
        _, assignments, unsat = self._solve(0, self.formula, assignments)
        sat = not unsat
        return sat, assignments


def read_sat_input(input_path):
    COMMENT_LINE_PATTERN='c.*'
    INFO_LINE_PATTERN='p\s*cnf\s*(\d*)\s*(\d*)'
    comment_line_regex = re.compile(COMMENT_LINE_PATTERN)
    info_line_regex = re.compile(INFO_LINE_PATTERN)
    formula = []
    total_used_prop = set()
    num_props, num_clauses = 0, 0
    with open(input_path, 'r') as input_file:
        for line in input_file.readlines():
            line = line.strip()
            if line == "%" or not line:
                continue
            if not comment_line_regex.match(line):
                infos = info_line_regex.match(line)
                if infos:
                    num_props = int(infos.group(1))
                    num_clauses = int(infos.group(2))
                else:
                    raw_props = line.rstrip('\n').split()
                    props = []
                    for prop in raw_props:
                        prop = int(prop)
                        if prop != 0:
                            props.append(prop)
                    total_used_prop = total_used_prop.union([abs(x) for x in props])
                    formula.append(props)
    return num_props, num_clauses, formula, total_used_prop

def check_correct(assignments, formula):
    for clause in formula:
        res = False
        for prop in clause:
            if prop < 0:
                res = res or (not assignments[abs(prop)])
            else:
                res = res or assignments[prop]
        if res == False:
            print("Wrong")
            return
    print("All the assignments are right!")

def run_sat_solver_DPLL(input_path):
    num_props, num_clauses, formula, total_used_prop = read_sat_input(input_path)
    input_name = os.path.basename(input_path)
    solver = DPLL(formula)
    start_time = datetime.datetime.now()
    sat, assignments = solver.solve_sat()
    end_time = datetime.datetime.now()
    sat_output = "SAT" if sat else "UNSAT"
    print(sat_output)
    final_res = {}
    if sat_output == "SAT":
        for key, value in assignments.items():
            final_res[key] = value
        for prop in total_used_prop:
            if prop not in assignments.keys():
                final_res[prop] = random.randint(0,1)
        final_res_sort = sorted(final_res.items(), key = lambda item: item[0])
        for assignment in final_res_sort:
            print(assignment[0], assignment[1])

        # check_correct(final_res, formula)
    print("Running Time:", end_time-start_time)