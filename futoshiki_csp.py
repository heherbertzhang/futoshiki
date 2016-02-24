# Look for #IMPLEMENT tags in this file. These tags indicate what has
# to be implemented.

'''
Construct and return Futoshiki CSP models.
'''

from cspbase import *
import itertools


def all_different_check(t):
    size = len(t)
    for i in range(size):
        j = i + 1
        while j < size:
            if t[i] == t[j]:
                return False
            j += 1
    return True


def check_constraint_add_tuples(constraint):
    domains = []
    for var in constraint.get_scope():
        domains.append(var.domain())
    sat_tup = []
    switch = {
        '>': lambda t: t[0] > t[1],
        '<': lambda t: t[0] < t[1],
        'not_equal': lambda t: not t[0] == t[1],
        'all_different': all_different_check
    }
    for t in itertools.product(*domains):
        if switch.get(constraint.name)(t):
            sat_tup.append(t)
    constraint.add_satisfying_tuples(sat_tup)


def futoshiki_csp_model_1(initial_futoshiki_board):
    '''Return a CSP object representing a Futoshiki CSP problem along with an
    array of variables for the problem. That is return

    futoshiki_csp, variable_array

    where futoshiki_csp is a csp representing futoshiki using model_1 and
    variable_array is a list of lists

    [ [  ]
      [  ]
      .
      .
      .
      [  ] ]

    such that variable_array[i][j] is the Variable (object) that you built to
    represent the value to be placed in cell i,j of the futoshiki board
    (indexed from (0,0) to (n-1,n-1))


    The input board is specified as a list of n lists. Each of the n lists
    represents a row of the board. If a 0 is in the list it represents an empty
    cell. Otherwise if a number between 1--n is in the list then this
    represents a pre-set board position.

    Each list is of length 2n-1, with each space on the board being separated
    by the potential inequality constraints. '>' denotes that the previous
    space must be bigger than the next space; '<' denotes that the previous
    space must be smaller than the next; '.' denotes that there is no
    inequality constraint.

    E.g., the board

    -------------------
    | > |2| |9| | |6| |
    | |4| | | |1| | |8|
    | |7| <4|2| | | |3|
    |5| | | | | |3| | |
    | | |1| |6| |5| | |
    | | <3| | | | | |6|
    |1| | | |5|7| |4| |
    |6> | |9| < | |2| |
    | |2| | |8| <1| | |
    -------------------
    would be represented by the list of lists

    [[0,'>',0,'.',2,'.',0,'.',9,'.',0,'.',0,'.',6,'.',0],
     [0,'.',4,'.',0,'.',0,'.',0,'.',1,'.',0,'.',0,'.',8],
     [0,'.',7,'.',0,'<',4,'.',2,'.',0,'.',0,'.',0,'.',3],
     [5,'.',0,'.',0,'.',0,'.',0,'.',0,'.',3,'.',0,'.',0],
     [0,'.',0,'.',1,'.',0,'.',6,'.',0,'.',5,'.',0,'.',0],
     [0,'.',0,'<',3,'.',0,'.',0,'.',0,'.',0,'.',0,'.',6],
     [1,'.',0,'.',0,'.',0,'.',5,'.',7,'.',0,'.',4,'.',0],
     [6,'>',0,'.',0,'.',9,'.',0,'<',0,'.',0,'.',2,'.',0],
     [0,'.',2,'.',0,'.',0,'.',8,'.',0,'<',1,'.',0,'.',0]]


    This routine returns Model_1 which consists of a variable for each cell of
    the board, with domain equal to [1,...,n] if the board has a 0 at that
    position, and domain equal [i] if the board has a fixed number i at that
    cell.

    Model_1 also contains BINARY CONSTRAINTS OF NOT-EQUAL between all relevant
    variables (e.g., all pairs of variables in the same row, etc.).

    All of the constraints of Model_1 MUST BE binary constraints (i.e.,
    constraints whose scope includes two and only two variables).
    '''

    variable_array = [[] for i in range(len(initial_futoshiki_board))]
    csp_variables = []
    full_domain = [i + 1 for i in range(len(initial_futoshiki_board))]
    for i, row in enumerate(initial_futoshiki_board):
        number = True
        j = 0
        for item in row:
            if number:
                if item == 0:
                    domain = list(full_domain)
                else:
                    domain = [item]
                var = Variable('V{},{}'.format(i, j), domain)
                variable_array[i].append(var)
                csp_variables.append(var)
                number = False
                j += 1
            else:
                number = True
    csp = CSP('Futoshiki-M1', csp_variables)

    # add constraints for row and column
    size = len(initial_futoshiki_board)
    for i, row in enumerate(initial_futoshiki_board):
        cur_item = 0
        for cur_item in range(size):
            j = cur_item + 1
            while j < size:
                c = Constraint('not_equal', [variable_array[i][cur_item], variable_array[i][j]])
                check_constraint_add_tuples(c)
                csp.add_constraint(c)
                j += 1
            # for column
            k = i + 1
            while k < size:
                c = Constraint('not_equal', [variable_array[i][cur_item], variable_array[k][cur_item]])
                check_constraint_add_tuples(c)
                csp.add_constraint(c)
                k += 1

    # create constraints for the board
    for i, row in enumerate(initial_futoshiki_board):
        j = -1  # keep track of the number index
        is_symbol = False
        for k, item in enumerate(row):
            if is_symbol:
                if not item == '.':
                    symbol_c = Constraint(item, [variable_array[i][j], variable_array[i][j + 1]])
                    check_constraint_add_tuples(symbol_c)
                    csp.add_constraint(symbol_c)
                is_symbol = False
            else:
                j += 1
                is_symbol = True
    return csp, variable_array


##############################

def futoshiki_csp_model_2(initial_futoshiki_board):
    '''Return a CSP object representing a futoshiki CSP problem along with an
    array of variables for the problem. That is return

    futoshiki_csp, variable_array

    where futoshiki_csp is a csp representing futoshiki using model_2 and
    variable_array is a list of lists

    [ [  ]
      [  ]
      .
      .
      .
      [  ] ]

    such that variable_array[i][j] is the Variable (object) that you built to
    represent the value to be placed in cell i,j of the futoshiki board
    (indexed from (0,0) to (n-1,n-1))

    The input board takes the same input format (a list of n lists of size 2n-1
    specifying the board) as futoshiki_csp_model_1.

    The variables of Model_2 are the same as for Model_1: a variable for each
    cell of the board, with domain equal to [1,...,n] if the board has a 0 at
    that position, and domain equal [n] if the board has a fixed number i at
    that cell.

    However, Model_2 has different constraints. In particular, instead of
    binary non-equals constaints Model_2 has 2*n all-different constraints:
    all-different constraints for the variables in each of the n rows, and n
    columns. Each of these constraints is over n-variables (some of these
    variables will have a single value in their domain). Model_2 should create
    these all-different constraints between the relevant variables, and then
    separately generate the appropriate binary inequality constraints as
    required by the board. There should be j of these constraints, where j is
    the number of inequality symbols found on the board.  
    '''
    variable_array = [[] for i in range(len(initial_futoshiki_board))]
    csp_variables = []
    full_domain = [i + 1 for i in range(len(initial_futoshiki_board))]
    for i, row in enumerate(initial_futoshiki_board):
        number = True
        j = 0
        for item in row:
            if number:
                if item == 0:
                    domain = list(full_domain)
                else:
                    domain = [item]
                var = Variable('V{},{}'.format(i, j), domain)
                variable_array[i].append(var)
                csp_variables.append(var)
                number = False
                j += 1
            else:
                number = True
    csp = CSP('Futoshiki-M2', csp_variables)

    # add all different constraints for row and column
    size = len(initial_futoshiki_board)
    for i, row in enumerate(initial_futoshiki_board):
        c = Constraint('all_different', variable_array[i])
        check_constraint_add_tuples(c)
        csp.add_constraint(c)

    for j in range(size):
        vars = [row[j] for row in variable_array]
        c = Constraint('all_different', vars)
        check_constraint_add_tuples(c)
        csp.add_constraint(c)

    # create constraints for the board
    for i, row in enumerate(initial_futoshiki_board):
        j = -1  # keep track of the number index
        is_symbol = False
        for k, item in enumerate(row):
            if is_symbol:
                if not item == '.':
                    symbol_c = Constraint(item, [variable_array[i][j], variable_array[i][j + 1]])
                    check_constraint_add_tuples(symbol_c)
                    csp.add_constraint(symbol_c)
                is_symbol = False
            else:
                j += 1
                is_symbol = True
    return csp, variable_array
