import re

from cdcl_wl import CDCL_WL
from cnf import CNF

# definition of variables and basic functions
BLUE = 0
GREEN = 1
RED = 2
WHITE = 3
YELLOW = 4


def color(house_id, color): return ((house_id) + 5 * (color))


BRIT = 5
DANE = 6
GERMAN = 7
NORWEGIAN = 8
SWEDE = 9


def lives(house_id, nationality): return ((house_id) + 5 * (nationality))


BEER = 10
COFFEE = 11
MILK = 12
TEA = 13
WATER = 14


def drinks(house_id, drink): return ((house_id) + 5 * (drink))


BLENDS = 15
BLUEMASTER = 16
DUNHILL = 17
PALLMALL = 18
PRINCE = 19


def smokes(house_id, cigarette): return ((house_id) + 5 * (cigarette))


BIRD = 20
CAT = 21
DOG = 22
FISH = 23
HORSE = 24


def pets(house_id, pet): return ((house_id) + 5 * (pet))


# format of cnf file
COMMENT_LINE_PATTERN = 'c.*'
INFO_LINE_PATTERN = 'p\s*cnf\s*(\d*)\s*(\d*)'


def gen_einstein():

    # open the einstein cnf file
    es = open("einstein.cnf", "w")
    es.write("p cnf 125 893\n")  # actual clauses: 893

    # at least one house per color

    for c in range(5):
        # every house has a color
        for h in range(1, 6):
            es.write("%d " % color(h, c))
        es.write("0\n")

        for h in range(1, 6):
            for h2 in range(1, h):  # a color can be used once
                es.write("-%d -%d 0\n" % (color(h, c), color(h2, c)))
            for c2 in range(0, 5):
                if (c2 != c):  # a house can have only one color.
                    es.write("-%d -%d 0\n" % (color(h, c), color(h, c2)))

    for p in range(5):
        # every house has a pet
        for h in range(1, 6):
            es.write("%d " % (pets(h, p) + 25))
        es.write("0\n")

        for h in range(1, 6):
            for h2 in range(1, h):  # a pet can be used once
                es.write("-%d -%d 0\n" % (pets(h, p) + 25, pets(h2, p) + 25))
            for p2 in range(0, 5):
                if (p2 != p):  # a house can have only one pet.
                    es.write("-%d -%d 0\n" %
                             (pets(h, p) + 25, pets(h, p2) + 25))

    for n in range(5):
        # every house has a nationality
        for h in range(1, 6):
            es.write("%d " % (lives(h, n) + 50))
        es.write("0\n")

        for h in range(1, 6):
            for h2 in range(1, h):  # a nationality can be used once
                es.write("-%d -%d 0\n" % (lives(h, n) + 50, lives(h2, n) + 50))
            for n2 in range(0, 5):
                if (n2 != n):  # a house can have only one nationality.
                    es.write("-%d -%d 0\n" % (lives(h, n) +
                                              50, lives(h, n2) + 50))

    for d in range(5):
        # every house has a drink
        for h in range(1, 6):
            es.write("%d " % (drinks(h, d) + 75))
        es.write("0\n")

        for h in range(1, 6):
            for h2 in range(1, h):  # a drink can be used once
                es.write("-%d -%d 0\n" %
                         (drinks(h, d) + 75, drinks(h2, d) + 75))
            for d2 in range(0, 5):
                if (d2 != d):  # a house can have only one drink.
                    es.write("-%d -%d 0\n" %
                             (drinks(h, d) + 75, drinks(h, d2) + 75))

    for cg in range(5):
        # every house has a cigar
        for h in range(1, 6):
            es.write("%d " % (smokes(h, cg) + 100))
        es.write("0\n")

        for h in range(1, 6):
            for h2 in range(1, h):  # a cigar can be used once
                es.write("-%d -%d 0\n" % (smokes(h, cg) +
                                          100, smokes(h2, cg) + 100))
            for cg2 in range(0, 5):
                if (cg2 != cg):  # a house can have only one cigar.
                    es.write("-%d -%d 0\n" % (smokes(h, cg) +
                                              100, smokes(h, cg2) + 100))

    # The Brit lives in the red house
    for h in range(1, 6):
        es.write("-%d %d 0\n" % (lives(h, BRIT), color(h, RED)))
        es.write("%d -%d 0\n" % (lives(h, BRIT), color(h, RED)))

    # The Swede keeps dogs as pets
    for h in range(1, 6):
        es.write("-%d %d 0\n" % (lives(h, SWEDE), pets(h, DOG)))
        es.write("%d -%d 0\n" % (lives(h, SWEDE), pets(h, DOG)))

    # The Dane drinks tea
    for h in range(1, 6):
        es.write("-%d %d 0\n" % (lives(h, DANE), drinks(h, TEA)))
        es.write("%d -%d 0\n" % (lives(h, DANE), drinks(h, TEA)))

    # The green house is on the left of the white house
    for h in range(1, 6):
        for h2 in range(5, 0, -1):
            # Out of range - both cannot be beside each other at same time
            if ((h2 >= h - 1) and (h2 <= h)):
                pass
            else:
                es.write("-%d -%d 0\n" % (color(h, WHITE), color(h, GREEN)))

    # The green house owner drinks coffee
    for h in range(1, 6):
        es.write("-%d %d 0\n" % (color(h, GREEN), drinks(h, COFFEE)))
        es.write("%d -%d 0\n" % (color(h, GREEN), drinks(h, COFFEE)))

    # The person who smokes Pall Mall rears birds
    for h in range(1, 6):
        es.write("-%d %d 0\n" % (smokes(h, PALLMALL), pets(h, BIRD)))
        es.write("%d -%d 0\n" % (smokes(h, PALLMALL), pets(h, BIRD)))

    # The owner of YELLOW house smokes Dunhill
    for h in range(1, 6):
        es.write("-%d %d 0\n" % (color(h, YELLOW), smokes(h, DUNHILL)))
        es.write("%d -%d 0\n" % (color(h, YELLOW), smokes(h, DUNHILL)))

    # The man living in the center house drinks milk
    es.write("%d 0\n" % drinks(3, MILK))

    # The Norwegian lives in the first house
    es.write("%d 0\n" % lives(1, NORWEGIAN))

    # The man who smokes Blends lives next to the one who keeps cats
    es.write("-%d %d 0\n" % (smokes(1, BLENDS), pets(2, CAT)))
    es.write("-%d %d 0\n" % (smokes(5, BLENDS), pets(4, CAT)))
    for h in range(2, 5):
        es.write("-%d %d %d 0\n" %
                 (smokes(h, BLENDS), pets(h-1, CAT), pets(h+1, CAT)))

    # The man who keeps the HORSE lives next to the one who smokes Dunhill
    es.write("-%d %d 0\n" % (pets(1, HORSE), smokes(2, DUNHILL)))
    es.write("-%d %d 0\n" % (pets(5, HORSE), smokes(4, DUNHILL)))
    for h in range(2, 5):
        es.write("-%d %d %d 0\n" %
                 (pets(h, HORSE), smokes(h-1, DUNHILL), smokes(h+1, DUNHILL)))

    # The owner who smokes BLUEMASTER drinks beer.
    for h in range(1, 6):
        es.write("-%d %d 0\n" % (smokes(h, BLUEMASTER), drinks(h, BEER)))
        es.write("%d -%d 0\n" % (smokes(h, BLUEMASTER), drinks(h, BEER)))

    # The German smokes Prince
    for h in range(1, 6):
        es.write("-%d %d 0\n" % (lives(h, GERMAN), smokes(h, PRINCE)))
        es.write("%d -%d 0\n" % (lives(h, GERMAN), smokes(h, PRINCE)))

    # The Norwegian lives next to the blue house
    es.write("-%d %d 0\n" % (lives(1, NORWEGIAN), color(2, BLUE)))
    es.write("-%d %d 0\n" % (lives(5, NORWEGIAN), color(4, BLUE)))
    for h in range(2, 5):
        es.write("-%d %d %d 0\n" %
                 (lives(h, NORWEGIAN), color(h+1, BLUE), color(h+1, BLUE)))

    # The man who smokes Blends has a neighbour who drinks water
    es.write("-%d %d 0\n" % (smokes(1, BLENDS), drinks(2, WATER)))
    es.write("-%d %d 0\n" % (smokes(5, BLENDS), drinks(4, WATER)))
    for h in range(2, 5):
        es.write("-%d %d %d 0\n" % (smokes(h, BLENDS),
                                    drinks(h - 1, WATER), drinks(h + 1, WATER)))

    # close the einstein cnf file
    es.close()


def read_input(input_path):
    print("Read input from file {}".format(input_path))

    comment_line_regex = re.compile(COMMENT_LINE_PATTERN)
    info_line_regex = re.compile(INFO_LINE_PATTERN)
    formula = []
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
                    print(num_props)
                    print(num_clauses)
                else:
                    raw_props = line.rstrip('\n').split()
                    props = []
                    for prop in raw_props:
                        prop = int(prop)
                        if prop != 0:
                            props.append(prop)
                    formula.append(props)
    return CNF(num_props, num_clauses, formula)


def get_resident_name(idx, dictionary):
    if idx in dictionary.keys():
        return dictionary[idx]
    else:
        return ""


if __name__ == "__main__":
    # generate einstein.cnf file
    gen_einstein()
    # read formulas
    cnf = read_input("einstein.cnf")
    print(cnf.formula)
    solver = CDCL_WL(cnf.formula, [])
    metrics = solver.solve()
    fish_house = 0
    for house_id in range(1, 6):
        if solver.assignments[pets(house_id, FISH)][0] == 1:
            fish_house = house_id
            print("House {} keeps the fish.".format(str(house_id)))
    owner = ""
    for nationality in [BRIT, SWEDE, DANE, NORWEGIAN, GERMAN]:
        if solver.assignments[lives(fish_house, nationality)][0] == 1:
            owner_id = nationality
    resident_names = {5: "Brit", 6: "Dane",
                      7: "German", 8: "Norwegian", 9: "Swede"}
    owner = get_resident_name(owner_id, resident_names)
    print("The {} keeps the fish.".format(owner))
