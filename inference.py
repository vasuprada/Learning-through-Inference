import sys
import csv


visited_goals = []
global_theta = {}
first_one = 0


class Clause:
    def __init__(self, literal, predicate, argument_list, no_arguments):
        self.literal = literal
        self.predicate = predicate
        self.argument_list = argument_list
        self.no_arguments = no_arguments


def parse_clause(clause):
    arguments = []
    predicate = clause.split("(")
    comma_no = predicate[1].count(",")

    if comma_no == 0:
        temp_arg = predicate[1].split(")")
        arguments.append(temp_arg[0])
    else:
        temp = predicate[1].split(",")
        for value in temp:
            if ")" in value:
                value_temp = value.split(")")
                arguments.append(value_temp[0])
            else:
                arguments.append(value)

    clause_object = Clause(clause, predicate[0], arguments, comma_no + 1)
    return clause_object


def unify(rhs, query, theta):
    # Unify(A(x,x,z), A(John, Bob, Alice), {}) --> x,y,z John,Bob,Alice
    arguments_query = query.argument_list

    for i in range(0, len(rhs.argument_list)):
        if rhs.argument_list[i] not in theta.keys():
            if arguments_query[i].islower():
                pass
            else:
                theta[rhs.argument_list[i]] = arguments_query[i]
        else:
            if theta[rhs.argument_list[i]] != arguments_query[i]:
                theta = {}
                break

    return theta


def fol_bc_ask(kb, query):
    sub = {}
    global visited_goals
    visited_goals = []
    inference = fol_bc_or(kb, query, sub)
    # print inference
    output_file_handle.write(inference + '\n')

def fol_bc_or(kb, goal, theta):
    keys = ""
    flag = 0
    all_facts = 1
    for arg in goal.argument_list:
        if arg[0].islower():
            all_facts = 0
            break
    if all_facts == 1:
        predicate = goal.predicate
        to_add = predicate + "("
        for i in range(0, goal.no_arguments-1):
            to_add += goal.argument_list[i] + ","
        to_add += goal.argument_list[goal.no_arguments - 1] + ")"

        if to_add in visited_goals:
            return 'FALSE'
        else:
            visited_goals.append(to_add)

        if goal.predicate in facts.keys():
            for arg_list in facts[goal.predicate]:
                lis = arg_list.split("(")
                lis_args = lis[1].split(")")
                fact_arguments = lis_args[0].split(",")
                if cmp(goal.argument_list, fact_arguments) == 0:
                    return 'TRUE'

    # Check unify (P2)
    for keys in kb.keys():
        if goal.predicate == keys:
            flag = 1
            break
    # NO RULE MATCHES
    if flag == 1:
        # UNIFY AND SUBSTITUTE
        rule_set = kb[keys]
        for rule in rule_set:
            if rule[0].no_arguments != goal.no_arguments:
                return 'FALSE'
            else:
                answer = fol_bc_and(kb, rule[1], unify(rule[0], goal, theta))
                if answer == 'TRUE':
                    return answer
    return 'FALSE'


def substitute(theta, each_goal):
    temp_list = []
    subst_list = each_goal.argument_list
    for argument in subst_list:
        if argument not in theta.keys():
            temp_list.append(argument)
        else:
            temp_list.append(theta[argument])
    literal = each_goal.literal
    predicate = each_goal.predicate
    no_arguments = each_goal.no_arguments

    # Rebuild a string
    new_goal = Clause(literal, predicate, temp_list, no_arguments)
    return new_goal


def fol_bc_and(kb, goals, theta):

    temp_first = ""
    temp_theta = {}
    temp_theta = theta.copy()
    temp_theta1 = []
    all_correct = 1
    no_facts_present = 1

    if theta is {}:
        return 'FALSE'

    if type(goals) is not list:

        if goals.predicate in facts.keys():
            for each_list in facts[goals.predicate]:

                temp_theta = theta.copy()
                temp_first = substitute(theta, goals)

                all_correct = 1
                lis = each_list.split("(")
                lis_args = lis[1].split(")")
                fact_arguments = lis_args[0].split(",")

                for i in range(0, temp_first.no_arguments):
                    if temp_first.argument_list[i][0].islower():
                        temp_theta[temp_first.argument_list[i][0]] = fact_arguments[i]
                    else:
                        if temp_first.argument_list[i] != fact_arguments[i]:
                            all_correct = 0
                            break

                if all_correct == 1:
                    no_facts_present = 0
                    temp_theta1.append(temp_theta)

            if no_facts_present == 1:

                answer = fol_bc_or(kb, substitute(theta, goals), theta)

                if answer == 'TRUE':
                    return answer

            for theta_check in temp_theta1:

                answer = fol_bc_or(kb, substitute(theta_check, temp_first), theta_check)

                if answer == 'TRUE':
                    return answer
            return 'FALSE'

        else:
            answer = fol_bc_or(kb, substitute(theta, goals), theta)
            if answer == 'TRUE':
                    return answer

    else:

        last_call_obj = ""
        rest = []
        first = goals[0]
        last_call = 0
        for i in range(1, len(goals)):
            rest.append(goals[i])
        if len(rest) == 1:
            last_call_obj = rest[0]
            last_call = 1

        if first.predicate in facts.keys():

            for each_list in facts[first.predicate]:

                temp_theta = theta.copy()
                temp_first = substitute(theta, first)

                all_correct = 1
                lis = each_list.split("(")
                lis_args = lis[1].split(")")
                fact_arguments = lis_args[0].split(",")

                for i in range(0, temp_first.no_arguments):
                    if temp_first.argument_list[i][0].islower():
                        temp_theta[temp_first.argument_list[i][0]] = fact_arguments[i]
                    else:
                        if temp_first.argument_list[i] != fact_arguments[i]:
                            all_correct = 0
                            break

                if all_correct == 1:
                    no_facts_present = 0
                    temp_theta1.append(temp_theta)

            if no_facts_present == 1:
                answer = fol_bc_or(kb, substitute(theta, first), theta)

                if answer == 'TRUE':
                    return answer

            for theta_check in temp_theta1:

                answer = fol_bc_or(kb, substitute(theta_check, temp_first), theta_check)

                if answer == 'TRUE':

                    if last_call == 1:
                        child_call = fol_bc_and(kb, last_call_obj, theta_check)

                    else:
                        child_call = fol_bc_and(kb, rest, theta_check)

                    if child_call == 'TRUE':
                        return 'TRUE'

        else:
            answer = fol_bc_or(kb, substitute(theta, first), theta)
            if answer == 'TRUE':
                return answer

    return 'FALSE'

with open(sys.argv[2]) as file_handle:
    reader = csv.reader(file_handle, delimiter='\n')
    lis_input = []
    for row in reader:
        lis_input.append(row)

OutputFileName = "output.txt"
output_file_handle = open(OutputFileName, 'w')

# NO_OF_QUERIES
query_list = []
no_queries = int(lis_input[0][0])

# QUERIES
x = 0
for x in range(1, no_queries + 1):
    query_list.append(lis_input[x][0])


# NO_OF_RULES
no_rules = int(lis_input[x + 1][0])
# FACTS
facts = {}
# MAP FOR INDEXING CLAUSES
KB = {}
# PARSING RULES
y = 0
value_list = []
conjunct_object_list = []
for y in range(x + 2, x + no_rules + 2):
    p = lis_input[y][0]

    if '=>' in p:
        parts_of_rule = p.split(' => ')

        consequent = parts_of_rule[1]
        antecedent = parts_of_rule[0]
        predicate_c = consequent.split("(")
        consequent_object = parse_clause(consequent)
        value_list.append(consequent_object)

        if " ^ " in antecedent:
            conjuncts = antecedent.split(" ^ ")
            for clause_c in conjuncts:
                conjunct_object = parse_clause(clause_c)
                conjunct_object_list.append(conjunct_object)
            value_list.append(conjunct_object_list)

            conjunct_object_list = []

        else:
            antecedent_object = parse_clause(antecedent)
            value_list.append(antecedent_object)

        KB.setdefault(predicate_c[0], []).append(value_list)
        value_list = []

    else:
        # Adding Literals like B(John,Bob) to Facts
        predicate_f = p.split("(")
        facts.setdefault(predicate_f[0], []).append(p)

query_object_list = []
# Make Queries also objects
for query_item in query_list:
    query_object = parse_clause(query_item)
    query_object_list.append(query_object)

for query_obj in query_object_list:
    fol_bc_ask(KB, query_obj)
