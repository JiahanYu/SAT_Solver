import datetime
import math
import random
from collections import Counter
from itertools import chain
import os
import re

class CDCL:
    def __init__(self, formula, branching_heuristic=None):
        self.formula = formula
        self.atomic_props = self.get_atomic_props(formula)
        self.pick_branching_num = 0
        self.branching_heuristic = branching_heuristic
        self.assignments, self.level_assignments = {}, {}
        self.implication_graph, self.level_forced_assign_var_map = {}, {}
        self.init_var_clause_map(self.atomic_props)
        self.newly_assigned_vars = []
        self.num_conflicts = 0
        self.branching_fn = self.choose_branching_heuristic(branching_heuristic)

    def get_atomic_props(self, formula):
        atomic_props = set()
        for clause in formula:
            [atomic_props.add(abs(lit)) for lit in clause]
        return list(atomic_props)
    
    def hash_clause(self, clause):
        return "#".join([str(lit) for lit in clause])

    def init_var_clause_map(self, atomic_props):
        self.hash_clause_map = {}
        self.lit_hash_map = {}
        self.clause_idx_hash_map = {}
        for i, clause in enumerate(self.formula):
            clause_hash = self.hash_clause(clause)
            self.hash_clause_map[clause_hash] = clause
            self.clause_idx_hash_map[i] = clause_hash
        for var in self.atomic_props:
            self.lit_hash_map[var] = []
            self.lit_hash_map[-var] = []
        for clause in self.formula:
            for lit in clause:
                self.lit_hash_map[lit].append(self.hash_clause(clause))
    
    def compute_val(self, lit, assignments):
        if abs(lit) not in assignments:
            return -1
        elif assignments[abs(lit)][0] == 1:
            return 1 if lit > 0 else 0
        return 1 if lit < 0 else 0

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
    
    def get_var_counts(self, formula):
        var_counts = Counter()
        for clause in formula:
            for lit in clause:
                var = abs(lit)
                var_counts[var] = 0 if var not in var_counts else var_counts[var]
                var_counts[var] += 1
        return var_counts

    def heuristic_moms(self, formula, assignments, k=1):
        min_clause_size = min([len(clause) for clause in formula])
        min_formula = [clause for clause in formula if len(clause) == min_clause_size]
        return self.heuristic_maxo(min_formula, assignments, k)

    def heuristic_maxo(self, formula, assignments, k=1):
        var_counts = self.get_var_counts(formula)
        return [s[0] for s in var_counts.most_common(k)]

    def heuristic_mams(self, formula, assignments, k=1):
        min_clause_size = min([len(clause) for clause in formula])
        min_formula = [clause for clause in formula if len(clause) == min_clause_size]
        moms_counts = self.get_var_counts(min_formula)
        maxo_counts = self.get_var_counts(formula)
        total_counts = Counter()
        for var, cnt in maxo_counts.items():
            total_cnt = cnt + moms_counts[var] if var in moms_counts else cnt
            total_counts[var] = total_cnt
        return [s[0] for s in total_counts.most_common(k)]

    def compute_jw_scores(self, formula):
        jw_scores = Counter()
        for clause in formula:
            for lit in clause:
                var = abs(lit)
                jw_scores[var] = jw_scores[var] if var in jw_scores else 0
                jw_scores[var] += 2**(-len(clause))
        return jw_scores

    def heuristic_jw(self, formula, assignments, k=1):
        jw_scores = self.compute_jw_scores(formula)
        return [s[0] for s in jw_scores.most_common(k)]

    def heuristic_2clause(self, formula, assignments, k=1):
        var_counts_2clause = Counter()
        for clause in formula:
            if len(clause) == 2:
                for lit in clause:
                    var = abs(lit) 
                    var_counts_2clause[var] = var_counts_2clause[var] if var in var_counts_2clause else 0
                    var_counts_2clause[var] += 1
        return self.heuristic_random(formula, assignments) if len(var_counts_2clause) == 0 else [s[0] for s in var_counts_2clause.most_common(k)]

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

    def get_num_unit_propagation(self, formula, lit):
        num_unit_propagations = 0
        resolving_lits = [lit]
        resolved_formula = formula
        result_code = 0
        while len(resolving_lits) > 0:
            resolving_lit = resolving_lits.pop()
            resolved_formula, _, unsat = self.resolve_by_lit(resolved_formula, resolving_lit)
            if unsat:
                result_code = -1
                break
            if len(resolved_formula) == 0:
                result_code = 1
                break
            unit_lits = [clause[0] for clause in resolved_formula if len(clause) == 1]
            num_unit_propagations += len(unit_lits)
            resolving_lits = unit_lits + resolving_lits
            resolving_lits = list(set(resolving_lits))
        return num_unit_propagations, result_code

    def heuristic_up(self, formula, assignments, k=1):
        assigned_vars = assignments.keys()
        unassigned_vars = [var for var in self.atomic_props if var not in assigned_vars]
        var_up_map = Counter()
        for var in unassigned_vars:
            num_up_from_var, _ = self.get_num_unit_propagation(formula, var)
            num_up_from_neg_var, _ = self.get_num_unit_propagation(formula, -var)
            var_up_map[var] = num_up_from_var + num_up_from_neg_var

        return [s[0] for s in var_up_map.most_common(k)]

    def _heuristic_up(self, formula, vars, k=1):
        var_up_map = Counter()
        for var in vars:
            num_up_from_var, _ = self.get_num_unit_propagation(formula, var)
            num_up_from_neg_var, _ = self.get_num_unit_propagation(formula, -var)
            var_up_map[var] = num_up_from_var + num_up_from_neg_var            
        return [s[0] for s in var_up_map.most_common(k)]

    def heuristic_gup(self, formula, assignments, k=1):
        assigned_vars = assignments.keys()
        unassigned_vars = [var for var in self.atomic_props if var not in assigned_vars]
        var_up_map = Counter()
        for var in unassigned_vars:
            num_up_from_var, status_code = self.get_num_unit_propagation(formula, var)
            if status_code != 0:
                return [var]
            num_up_from_neg_var, status_code = self.get_num_unit_propagation(formula, -var)
            if status_code != 0:
                return [var]
            var_up_map[var] = num_up_from_var + num_up_from_neg_var
        return [s[0] for s in var_up_map.most_common(k)]

    def heuristic_sup(self, formula, assignments, k=4):
        top_k_maxo = self.heuristic_maxo(formula, assignments, k)
        top_k_moms = self.heuristic_moms(formula, assignments, k)
        top_k_mams = self.heuristic_mams(formula, assignments, k)
        top_k_jw = self.heuristic_jw(formula, assignments, k)
        top_k = [x[0] for x in Counter(top_k_maxo + top_k_moms + top_k_mams + top_k_jw).most_common(k)]
        return self._heuristic_up(formula, top_k)

    def heuristic_random(self, formula, assignments):
        assigned_vars = assignments.keys()
        unassigned_vars = [var for var in self.atomic_props if var not in assigned_vars]
        return [random.choice(unassigned_vars)]

    def heuristic_ordered(self, formula, assignments):
        for var in self.atomic_props:
            if var not in assignments:
                return [var]
        return [0]

    def init_vsids(self):
        self.var_activities = {}
        self.var_decided_vals = {}
        self.decay_val = 0.8
        self.decay_period = 1
        self.bonus_coeff = 1.2
        self.var_activities = dict(self.compute_jw_scores(self.formula))
        self.bonus_score = max(list(self.var_activities.values()))/2.0
    
    def heuristic_vsids(self, formula, assignments, k=1):
        remaining_var_activities = {}
        for var, activity in self.var_activities.items():
            if var not in self.assignments:
                remaining_var_activities[var] = activity
        return [x[0] for x in sorted(remaining_var_activities.items(), key=lambda x: x[1])][:-k]
    
    def get_assign_value_vsids(self, next_var):
        if next_var not in self.var_decided_vals:
            next_var_val = 1
            self.var_decided_vals[next_var] = next_var_val
        else:
            next_var_val = self.var_decided_vals[next_var]
        return next_var_val
    
    def choose_branching_heuristic(self, branching_heuristic):
        if branching_heuristic == "mvsids" or branching_heuristic == "cvsids":
            self.init_vsids()
            return self.heuristic_vsids
        if branching_heuristic == "order":
            return self.heuristic_ordered
        if branching_heuristic == "random":
            return self.heuristic_random
        if branching_heuristic == "2clause":
            return self.heuristic_2clause
        if branching_heuristic == "maxo":
            return self.heuristic_maxo
        if branching_heuristic == "moms":
            return self.heuristic_moms
        if branching_heuristic == "mams":
            return self.heuristic_mams
        if branching_heuristic == "jw":
            return self.heuristic_jw
        if branching_heuristic == "up":
            return self.heuristic_up
        if branching_heuristic == "gup":
            return self.heuristic_gup
        if branching_heuristic == "sup":
            return self.heuristic_sup
        return self.heuristic_random

    def assign_next_var(self, formula, assignments, shortened=False):
        self.pick_branching_num += 1
        if shortened:
            formula = self.shorten_formula(formula, assignments)
        assert [] not in formula
        if len(formula) == 0:
            next_var = 0
        else:
            next_var = self.branching_fn(formula, assignments)[0]
        if next_var != 0:
            if self.branching_heuristic == "cvsids" or self.branching_heuristic == "mvsids":
                next_var_val = self.get_assign_value_vsids(next_var)
            else:
                next_var_val = 1
        else:
            next_var_val = -1
        return next_var, next_var_val

    def assign_var(self, var, level, value):
        if var in self.assignments:
            if self.assignments[var][0] != value: 
                return False
            return True
        self.assignments[var] = (value, level)
        if level not in self.level_assignments:
            self.level_assignments[level] = []
        self.level_assignments[level].append(var)
        return True
    
    def force_assign_var(self, level):
        next_var, next_var_val = self.assign_next_var(self.formula, self.assignments, True)
        if next_var == 0:
            return True, next_var
        if level not in self.level_assignments:
            self.level_assignments[level] = []
        self.assign_var(next_var, level, next_var_val)
        self.level_forced_assign_var_map[level] = next_var
        return False, next_var
    
    def update_implication_graph(self, unassigned_lit, parents):
        if unassigned_lit in self.implication_graph:
            raise Exception("Unassigned lit {} already exists in implication graph.".format(unassigned_lit))
        self.implication_graph[unassigned_lit] = parents
    
    def update_newly_assigned_vars(self, vars, force):
        if force:
            self.newly_assigned_vars = vars
        else:
            for v in vars:
                if v not in self.newly_assigned_vars:
                    self.newly_assigned_vars = [v] + self.newly_assigned_vars
    
    def get_involved_clauses(self, lit):
        return [self.hash_clause_map[h] for h in self.lit_hash_map[lit]]
    
    def check_clause_status_wrapper(self, clause_hash):
        clause = self.hash_clause_map[clause_hash]
        clause_values = [self.compute_val(lit, self.assignments) for lit in clause]
        if 1 not in clause_values:  
            if -1 not in clause_values:
                return "conflict", clause, 0
            if sum(clause_values) == -1:
                unassigned_lit = clause[clause_values.index(-1)]
                return "unit", clause, unassigned_lit
            return "unassaigned", [], 0
        return "sat", [], 0

    def assign_pure_vars(self, level):
        if level-1 not in self.level_assignments:
            checking_vars = self.atomic_props
        else:
            last_assigned_vars = self.level_assignments[level-1]
            checking_vars = set()
            for var in last_assigned_vars:
                true_lit = var if self.assignments[var][0] > 0 else -var
                for clause in self.get_involved_clauses(true_lit):
                    checking_vars.union(set([abs(lit) for lit in clause]))
            checking_vars = list(checking_vars)
        for var in checking_vars:
            if var not in self.assignments:
                has_pos_lit = False
                for clause_hash in self.lit_hash_map[var]:
                    if self.check_clause_status_wrapper(clause_hash)[0] != "sat":
                        has_pos_lit = True
                if not has_pos_lit:
                    assignable = self.assign_var(var, level, 0)
                    if not assignable:
                        raise Exception("Pure var must be assignable")
                    self.update_newly_assigned_vars([var], False)
                    continue
                has_neg_lit = False
                for clause_hash in self.lit_hash_map[-var]:
                    if self.check_clause_status_wrapper(clause_hash)[0] != "sat":
                        has_neg_lit = True
                if not has_neg_lit:
                    assignable = self.assign_var(var, level, 1)
                    self.update_newly_assigned_vars([var], False)

    def assign_lit_from_clause(self, unassigned_lit, clause, level):
        assigned_value = 1 if unassigned_lit > 0 else 0
        var = abs(unassigned_lit)
        self.assign_var(var, level, assigned_value)
    
    def deduce(self, level):
        while len(self.newly_assigned_vars) > 0:
            var = self.newly_assigned_vars.pop()
            true_lit = var if self.assignments[var][0] > 0 else -var
            false_lit = -true_lit
            for clause_hash in self.lit_hash_map[false_lit]:
                status, clause, unassigned_lit = self.check_clause_status_wrapper(clause_hash)
                if status == "conflict":
                    self.update_implication_graph(0, clause)
                    return True
                if status == "unit":
                    self.assign_lit_from_clause(unassigned_lit, clause, level)
                    self.update_implication_graph(unassigned_lit, [-lit for lit in clause if lit != unassigned_lit])
                    self.update_newly_assigned_vars([abs(unassigned_lit)], False)
        return False

    def get_learnt_clause(self, analysing_clause):
        return [-lit for lit in analysing_clause]
    
    def conflict_analyse(self, level):
        temp_level_lits_map = {}
        analysing_clause = [-lit for lit in self.implication_graph[0]]
        for lit in analysing_clause:
            lvl = self.assignments[abs(lit)][1]
            if lvl not in temp_level_lits_map:
                temp_level_lits_map[lvl] = []
            temp_level_lits_map[lvl].append(lit)
        while len(temp_level_lits_map[level]) > 1:
            next_lit = temp_level_lits_map[level][1] if abs(temp_level_lits_map[level][0]) == self.level_forced_assign_var_map[level] else temp_level_lits_map[level][0]
            for parent in self.implication_graph[next_lit]:
                parent_lvl = self.assignments[abs(parent)][1]
                if parent_lvl not in temp_level_lits_map:
                    temp_level_lits_map[parent_lvl] = []
                if -parent in temp_level_lits_map[parent_lvl]:
                    raise Exception("Learnt clause must not have 2 opposite lits")
                if parent not in temp_level_lits_map[parent_lvl]:
                    temp_level_lits_map[parent_lvl].append(parent)
            temp_level_lits_map[level].remove(next_lit)
            if self.branching_heuristic == "mvsids":
                self.var_activities[abs(next_lit)] += self.bonus_score
        learnt_clause = self.get_learnt_clause(list(chain.from_iterable(temp_level_lits_map.values())))
        levels = [self.assignments[abs(lit)][1] for lit in learnt_clause]
        backtrack_level = 0 if len(levels) < 2 else sorted(levels)[-2]
        return learnt_clause, backtrack_level
        
    def backtrack(self, backtrack_level, current_level):
        forced_assign_var = self.level_forced_assign_var_map[backtrack_level] if backtrack_level != 0  else -1
        forced_assign_var_value = self.assignments[forced_assign_var][0] if backtrack_level != 0 else -1
        for level in range(backtrack_level, current_level+1):
            if level != 0:
                assigned_aps = self.level_assignments[level]
                for var in assigned_aps:
                    del self.assignments[var]
                    if var in self.implication_graph:
                        del self.implication_graph[var]
                    if -var in self.implication_graph:
                        del self.implication_graph[-var]
                del self.level_assignments[level]
                del self.level_forced_assign_var_map[level]
        del self.implication_graph[0]
        return forced_assign_var, forced_assign_var_value
    
    def update_learnt_clause(self, learnt_clause):
        clause_hash = self.hash_clause(learnt_clause)
        self.hash_clause_map[clause_hash] = learnt_clause
        self.clause_idx_hash_map[len(self.clause_idx_hash_map)] = clause_hash
        self.formula.append(learnt_clause)
        for lit in learnt_clause:
            self.lit_hash_map[lit].append(clause_hash)
        return clause_hash
    
    def update_var_activities(self, learnt_clause):
        if self.branching_heuristic == "cvsids":
            for lit in learnt_clause:
                self.var_activities[abs(lit)] += self.bonus_score
        self.bonus_score *= math.ceil(self.bonus_coeff)
        if self.num_conflicts % self.decay_period == 0:
            for var in self.var_activities:
                self.var_activities[var] *= self.decay_val
            self.bonus_score *= math.ceil(self.decay_val)

    def solve_sat(self):
        self.level = 0
        sat = False
        while not sat:
            self.assign_pure_vars(self.level)
            conflict = self.deduce(self.level)
            if conflict:
                if self.level == 0:
                    sat = False
                    break
                self.num_conflicts += 1
                learnt_clause, backtrack_level = self.conflict_analyse(self.level)
                self.update_learnt_clause(learnt_clause)
                forced_assign_var, forced_assign_var_value = self.backtrack(backtrack_level, self.level)
                if backtrack_level != 0:
                    self.assign_var(forced_assign_var, backtrack_level, forced_assign_var_value)
                    self.level_forced_assign_var_map[backtrack_level] = forced_assign_var
                    self.update_newly_assigned_vars([forced_assign_var], True)
                else:
                    single_lit = learnt_clause[0]
                    self.assign_var(abs(single_lit), 0, 1 if single_lit > 0 else 0)
                    self.update_newly_assigned_vars([abs(single_lit)], True)
                self.level = backtrack_level
                if self.branching_heuristic == "cvsids" or self.branching_heuristic == "mvsids":
                    self.update_var_activities(learnt_clause)
            else:
                self.level += 1
                sat, next_var = self.force_assign_var(self.level)
                self.update_newly_assigned_vars([next_var], False)
        return sat, self.assignments, self.pick_branching_num

       
def read_input(input_path):
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

def run_sat_solver_CDCL(input_path, branching_heuristic):
    num_props, num_clauses, formula, total_used_prop = read_input(input_path)
    input_name = os.path.basename(input_path)
    solver = CDCL(formula, branching_heuristic)
    start_time = datetime.datetime.now()
    sat, assignments, pick_branching_num = solver.solve_sat()
    end_time = datetime.datetime.now()
    sat_output = "SAT" if sat else "UNSAT"
    print(sat_output)
    final_res = {}
    if sat_output == "SAT":
        for key, value in assignments.items():
            final_res[key] = value[0]
            # print(key, value[0])
        for prop in total_used_prop:
            if prop not in assignments.keys():
                final_res[prop] = random.randint(0,1)
        final_res_sort = sorted(final_res.items(), key=lambda item: item[0])
        for assignment in final_res_sort:
            print(assignment[0], assignment[1])
        
        # check_correct(final_res, formula)

    print("Running Time:", end_time-start_time)
    print("Branching Num:", pick_branching_num)
# run_sat_solver_CDCL("sat-examples/einstein.cnf", "jw")