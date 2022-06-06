import time
import random
import networkx as nx
import matplotlib.pyplot as plt

class Variable(object):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

Unassigned = Variable("Unassigned")

class Domain(list):
    def __init__(self, set):
        list.__init__(self, set)
        self._hidden = []
        self._states = []

    def reset_state(self):
        self.extend(self._hidden)
        del self._hidden[:]
        del self._states[:]

    def push_state(self):
        self._states.append(len(self))

    def pop_state(self):
        diff = self._states.pop() - len(self)
        if diff:
            self.extend(self._hidden[-diff:])
            del self._hidden[-diff:]

    def hide_value(self, value):
        list.remove(self, value)
        self._hidden.append(value)
        
class Constraint(object):
    def __init__(self, func, assigned=True):
        self._func = func
        self._assigned = assigned

    def __call__(self, variables, domains, assignments, forwardcheck=False, _unassigned=Unassigned,):
        parms = [assignments.get(x, _unassigned) for x in variables]
        missing = parms.count(_unassigned)
        if missing:
            return (self._assigned or self._func(variables, *parms)) and (
                not forwardcheck or
                self.forward_check(variables, domains, assignments)
            )
        return self._func(variables, *parms)

    def forward_check(self, variables, domains, assignments, _unassigned=Unassigned):
        unassigned_variable = _unassigned
        for variable in variables:
            if variable not in assignments:
                if unassigned_variable is _unassigned:
                    unassigned_variable = variable
                else:
                    break
        else:
            if unassigned_variable is not _unassigned:
                # Remove from the unassigned variable domain's all
                # values which break our variable's constraints.
                domain = domains[unassigned_variable]
                if domain:
                    for value in domain[:]:
                        assignments[unassigned_variable] = value
                        if not self(variables, domains, assignments, forwardcheck=False):
                            domain.hide_value(value)
                    del assignments[unassigned_variable]
                if not domain:
                    return False
        return True
    
class Problem(object):
    def __init__(self, solver=None):
        self._solver = solver
        self._constraints = []
        self._variables = {}

    def add_variable(self, variable, domain):
        domain = Domain(domain)
        self._variables[variable] = domain

    def add_variables(self, variables, domain):
        self.all_variables = variables
        for variable in variables:
            self.add_variable(variable, domain)

    def add_constraint(self, constraint, variables=None):
        constraint = Constraint(constraint)
        self._constraints.append((constraint, variables))

    def plot_map(self, edges):
        G = nx.Graph()
        G.add_nodes_from(self.all_variables)
        G.add_edges_from(edges)
        color_map = {}
        for node in self.all_variables:
            color_map[node] = self._solution[node]
        node_colors = [color_map.get(node) for node in G.nodes()]

        plt.title(self._solver.get_description())
        layout = nx.spring_layout(G, k = 1, seed=112)
        nx.draw(G, pos=layout, with_labels=True, node_color=node_colors, node_size=2000, cmap=plt.cm.rainbow)
        plt.show()

    def get_solution(self):
        domains, constraints, vconstraints = self._get_args()
        if not domains:
            return None
        self._solution = self._solver.get_solution(domains, constraints, vconstraints)
        return self._solution

    def _get_args(self):
        domains = self._variables.copy()
        constraints = self._constraints
        vconstraints = {}
        for variable in domains:
            vconstraints[variable] = []
        for constraint, variables in constraints:
            for variable in variables:
                vconstraints[variable].append((constraint, variables))
        for domain in domains.values():
            domain.reset_state()
        return domains, constraints, vconstraints

class Solver(object):
    def __init__(self):
        self.counter = 0

    def get_description(self):
        msg = "%s is an abstract class" % self.__class__.__name__
        raise NotImplementedError(msg)

    def get_solution(self, domains, constraints, vconstraints):
        msg = "%s is an abstract class" % self.__class__.__name__
        raise NotImplementedError(msg)


class MinConflictsSolver(Solver):
    def __init__(self, steps=1000):
        super().__init__()
        self._steps = steps

    def get_description(self):
        return "Minimum Conflicts Algorithm"

    def min_conflict(self, domains, vconstraints):
        self.counter = 0
        assignments = {}
        # Initial assignment
        for variable in domains:
            assignments[variable] = random.choice(domains[variable])
        for _ in range(self._steps):
            conflicted = False
            lst = list(domains.keys())
            random.shuffle(lst)
            for variable in lst:
                # Check if variable is not in conflict
                for constraint, variables in vconstraints[variable]:
                    self.counter = self.counter + 1
                    if not constraint(variables, domains, assignments):
                        break
                else:
                    continue
                # Variable has conflicts. Find values with less conflicts.
                mincount = len(vconstraints[variable])
                minvalues = []
                for value in domains[variable]:
                    assignments[variable] = value
                    count = 0
                    for constraint, variables in vconstraints[variable]:
                        self.counter = self.counter + 1
                        if not constraint(variables, domains, assignments):
                            count += 1
                    if count == mincount:
                        minvalues.append(value)
                    elif count < mincount:
                        mincount = count
                        del minvalues[:]
                        minvalues.append(value)
                # Pick a random one from these values.
                assignments[variable] = random.choice(minvalues)
                conflicted = True
            if not conflicted:
                return assignments
        return None

    def get_solution(self, domains, constraints, vconstraints):
        return self.min_conflict(domains, vconstraints)


class RecursiveBacktrackingSolver(Solver):
    def __init__(self, forwardcheck=True):
        super().__init__()
        self._forward_check = forwardcheck

    def get_description(self):
        return "Recursive Backtracking Algorithm with Forward check: %s" % self._forward_check

    def recursiveBacktracking(self, solutions, domains, vconstraints, assignments, single):
        # Minimum Remaining Values (MRV) heuristics
        lst = [(len(domains[variable]), variable) for variable in domains]
        lst.sort()
        for item in lst:
            if item[-1] not in assignments:
                # Found an unassigned variable. Let's go.
                break
        else:
            # No unassigned variables. We've got a solution.
            solutions.append(assignments.copy())
            return solutions

        variable = item[-1]
        assignments[variable] = Unassigned

        forwardcheck = self._forward_check
        if forwardcheck:
            pushdomains = [domains[x] for x in domains if x not in assignments]
        else:
            pushdomains = None

        for value in domains[variable]:
            assignments[variable] = value
            if pushdomains:
                for domain in pushdomains:
                    domain.push_state()
            for constraint, variables in vconstraints[variable]:
                self.counter = self.counter + 1
                if not constraint(variables, domains, assignments, pushdomains):
                    # Value is not good.
                    break
            else:
                # Value is good. Recurse and get next variable.
                self.recursiveBacktracking(solutions, domains, vconstraints, assignments, single)
                if solutions and single:
                    return solutions
            if pushdomains:
                for domain in pushdomains:
                    domain.pop_state()
        del assignments[variable]
        return solutions

    def get_solution(self, domains, constraints, vconstraints):
        self.counter = 0
        solutions = self.recursiveBacktracking([], domains, vconstraints, {}, False)
        return solutions and solutions[0] or None

regions = ['ASH', 'NA', 'AR', 'ALH', 'AS', 'JI', 'MA', 'ALB', 'ALQ', 'HA', 'ALM', 'TA', 'ALJ']
borders = [('ASH', 'NA'), ('ASH', 'AR'), ('ASH', 'ALH'), ('NA', 'AR'), ('NA', 'AS'), ('AR', 'ALH'),
           ('AR', 'AS'), ('AR', 'MA'), ('AR', 'ALQ'), ('AR', 'HA'), ('AR', 'ALM'), ('ALH', 'HA'),
           ('ALH', 'ALJ'), ('AS', 'JI'), ('AS', 'MA'), ('AS', 'ALB'), ('JI', 'MA'), ('MA', 'ALB'),
           ('MA', 'ALM'), ('ALQ', 'HA'), ('ALQ', 'ALM'), ('HA', 'ALM'), ('HA', 'TA'),
           ('HA', 'ALJ'), ('ALM', 'TA'),('TA', 'ALJ')]

colors = ["red", "blue", "green", "yellow"]


def check_border(variables, *args):
    zipped = list(zip(variables, args))
    return zipped[0][1] != zipped[1][1]

def solve_csp(solver):
    problem = Problem(solver)
    problem.add_variables(regions, colors)
    for node in regions:
        borders_per_node = [borders[index] for (index, a_tuple) in enumerate(borders) if a_tuple[0] == node]
        if borders_per_node:
            for border in borders_per_node:
                problem.add_constraint(check_border, list(border))

    start_time = time.time()
    problem.get_solution()
    end_time = (time.time() - start_time)
    print(f"Solution with {solver.get_description()} took {end_time} sec and {solver.counter} checks")
    problem.plot_map(borders)

if __name__ == "__main__":
    solvers = [RecursiveBacktrackingSolver(forwardcheck=False), RecursiveBacktrackingSolver(forwardcheck=True), MinConflictsSolver()]
    for solver in solvers:
        solve_csp(solver)