from z3 import *


def CreatePropositionName(i, j):
    # Creates the names for the propositions in the for pij
    # takes 2 ints and returns a string
    rtrn_str = "P" + str(i) + str(j)
    return rtrn_str


def CreatePropositions(n):
    # Creates all propositions for n-queens problem
    # arranges propositions in dictionary with tuples (i,j) for index
    # take 1 int and returns a dictionary
    propositions = dict()
    i = 1
    while (i <= n):
        j = 1
        while (j <= n):
            name = CreatePropositionName(i, j)
            index = (i, j)
            propositions.update({index: Bool(name)})
            j += 1
        i += 1
    return propositions


def Getpropositions(i, j, propositions_dict):
    # gets propositions from propositions dictionary
    # requires 2 ints and a dictionary, returns a propositions
    index = (i, j)
    return propositions_dict[index]


def CreateQ1(n, propositions_dict):
    # Creates proposition Q1 (1 queen in every row)
    i = 1
    rtrn_propositions = True
    while (i <= n):
        # loop for
        j = 1
        inner_disjunction = False
        while (j <= n):
            pij = Getpropositions(i, j, propositions_dict)
            if (j == 1):
                inner_disjunction = pij
            else:
                inner_disjunction = Or(inner_disjunction, pij)
            j = j + 1

        if (i == 1):
            rtrn_propositions = inner_disjunction
        else:
            rtrn_propositions = And(rtrn_propositions, inner_disjunction)
        i = i + 1

    return rtrn_propositions


def CreateQ2(n, propositions_dict):
    # Creates Q2(no more than 1 queen in a row)
    i = 1
    rtrn_proposition = True
    while (i <= n):
        j = 1
        conjunction_2 = True
        while (j <= (n - 1)):
            k = j + 1
            conjunction_1 = True
            while (k <= n):
                pij = Getpropositions(i, j, propositions_dict)
                pik = Getpropositions(i, k, propositions_dict)
                if (k == j + 1):
                    conjunction_1 = Or(Not(pij), Not(pik))
                else:
                    conjunction_1 = And(conjunction_1, Or(Not(pij), Not(pik)))
                k += 1

            if (j == 1):
                conjunction_2 = conjunction_1
            else:
                conjunction_2 = And(conjunction_2, conjunction_1)

            j += 1
        if (i == 1):
            rtrn_proposition = conjunction_2
        else:
            rtrn_proposition = And(rtrn_proposition, conjunction_2)
        i += 1
    return rtrn_proposition


def CreateQ3(n, propositions_dict):
    # Creates Q3 (no more than 1 queen in a column)
    j = 1
    rtrn_proposition = True
    while (j <= n):
        i = 1
        conjunction_2 = True
        while (i <= (n - 1)):
            k = i + 1
            conjunction_1 = True
            while (k <= n):
                pij = Getpropositions(i, j, propositions_dict)
                pkj = Getpropositions(k, j, propositions_dict)
                if (k == i + 1):
                    conjunction_1 = Or(Not(pij), Not(pkj))
                else:
                    conjunction_1 = And(conjunction_1, Or(Not(pij), Not(pkj)))
                k += 1
            if (i == 1):
                conjunction_2 = conjunction_1
            else:
                conjunction_2 = And(conjunction_2, conjunction_1)
            i += 1
        if (j == 1):
            rtrn_proposition = conjunction_2
        else:
            rtrn_proposition = And(rtrn_proposition, conjunction_2)
        j += 1
    return rtrn_proposition


def CreateQ4(n, propositions_dict):
    # creates Q4 (Ensures no diagonal has two queens)
    i = 2
    rtrn_proposition = True
    while (i <= n):
        j = 1
        k = 1
        conjunction_1 = True
        while ((i - k) >= 1):
            # Loop stops when i-k is not >= 1 because i-k decreases with each iteration,
            # and when i-k=1 all rows are accounted for
            pij = Getpropositions(i, j, propositions_dict)
            pikjk = Getpropositions((i - k), (j + k), propositions_dict)
            if (k == 1):
                conjunction_1 = Or(Not(pij), Not(pikjk))
            else:
                # Triggers after initial iteration, ensuring conjunction
                # builds upon itself
                conjunction_1 = And(conjunction_1, Or(Not(pij), Not(pikjk)))
            k += 1

        if (i == 2):
            rtrn_proposition = conjunction_1
        else:
            # Triggers after initial iteration of the outside loop,
            # ensuring proposition builds upon itself
            rtrn_proposition = And(rtrn_proposition, conjunction_1)

        if (n > 2):
            # Relevant for additional diagonals after the bottom corner
            # diagonal is reached (after i=n). j begins to increment to
            # account for these additional diagonals, while i=n and
            # does not change
            j = 2
            while (j < n):
                k = 1
                conjunction_2 = True
                while ((j + k) <= n and (i - k) > 0):
                    pij = Getpropositions(i, j, propositions_dict)
                    pikjk = Getpropositions((i - k), (j + k), propositions_dict)
                    if (k == 1):
                        conjunction_2 = Or(Not(pij), Not(pikjk))
                    else:
                        conjunction_2 = And(conjunction_2, Or(Not(pij), Not(pikjk)))
                    k += 1

                j += 1
                rtrn_proposition = And(rtrn_proposition, conjunction_2)
        i += 1
    return rtrn_proposition


def CreateQ5(n, propositions_dict):
    # creates Q5(Ensures no diagonal running downward has two queens)
    i = 1
    rtrn_proposition = True
    while (i < n):
        j = 1
        k = 1
        conjunction_1 = True
        while (i + k <= n):
            # Loop stops when i+k <= n because once i+k = n all diagonals
            # that don't require an increase in column size (j) are
            # accounted for
            pij = Getpropositions(i, j, propositions_dict)
            pikjk = Getpropositions((i + k), (j + k), propositions_dict)
            if (k == 1):
                conjunction_1 = Or(Not(pij), Not(pikjk))
            else:
                conjunction_1 = And(conjunction_1, Or(Not(pij), Not(pikjk)))
            k += 1
        if (i == 1):
            rtrn_proposition = conjunction_1
        else:
            rtrn_proposition = And(rtrn_proposition, conjunction_1)

        if (n > 2):
            # Triggers if n>2 because there are no additional
            # columns to account for if n=2. The following loops
            # increase j which accounts for the diagonals that begin
            # at a column size larger than 1. All of these diagonals
            # begin at row 1, so i remains 1.
            j = 2
            while (j < n):
                k = 1
                conjunction_2 = True
                while ((j + k) <= n and (i + k) <= n):
                    pij = Getpropositions(i, j, propositions_dict)
                    pikjk = Getpropositions((i + k), (j + k), propositions_dict)
                    if (k == 1):
                        conjunction_2 = Or(Not(pij), Not(pikjk))
                    else:
                        conjunction_2 = And(conjunction_2, Or(Not(pij), Not(pikjk)))
                    k += 1
                j += 1
                rtrn_proposition = And(rtrn_proposition, conjunction_2)
        i += 1
    return rtrn_proposition


def main():
    print('N-Queens Problem Solver', '\n')
    n = int(input("enter value for n: "))
    propositions_dict = CreatePropositions(n)
    Q1 = CreateQ1(n, propositions_dict)
    Q2 = CreateQ2(n, propositions_dict)
    Q3 = CreateQ3(n, propositions_dict)
    Q4 = CreateQ4(n, propositions_dict)
    Q5 = CreateQ5(n, propositions_dict)
    solver = Solver()
    solver.add(Q1, Q2, Q3, Q4, Q5)
    print('\n', solver.check(), 'isfiable', sep='')
    try:
        print('Truth assignment:\n', solver.model())
    except:
        print('Not solvable for n =', n)


main()
