from DPLL import run_sat_solver_DPLL
from CDCL import run_sat_solver_CDCL
import sys

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Please input which solver you want to use, DPLL or CDCL.")
    if sys.argv[1] == "DPLL":
        if len(sys.argv) < 3:
            print("Please input the file path you want to solve.")
        else:
            run_sat_solver_DPLL(sys.argv[2])
    elif sys.argv[1] == "CDCL":
        if len(sys.argv) < 3:
            print("Please input the file path you want to solve.")
        elif len(sys.argv) < 4:
            print("Warning: you didn't give the heuristics algorithm, random will be used.")
            run_sat_solver_CDCL(sys.argv[2], "random")
        else:
            heuristics_algorithm = {"order","random","2clause","maxo","moms","mams","up","gup","sup","jw", "mvsids", "cvsids"}
            if sys.argv[3] not in heuristics_algorithm:
                print("Sorry, we didn't provide this heuristics algorithm. Random will be used.")
                run_sat_solver_CDCL(sys.argv[2], "random")
            else:
                run_sat_solver_CDCL(sys.argv[2], sys.argv[3])
    else:
        print("We didn't provide this solver.")