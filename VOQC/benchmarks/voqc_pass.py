from qiskit.converters import circuit_to_dag
from qiskit.converters import dag_to_circuit
from qiskit.transpiler.basepasses import TransformationPass
from voqc import SQIR, load
from qiskit import QuantumCircuit
import re
import os


class VOQC(TransformationPass):
    def __init__(self, func = None, out = None):
        super().__init__()
        self.func = func if func else ["optimize"]
    def run(self, dag):
        circ = dag_to_circuit(dag)
        y =circ.qasm(formatted=False, filename="temp.qasm")
        t = self.function_call(self.func, "temp.qasm")
        os.remove("temp.qasm")
        u = self.rzq("temp2.qasm")
        #to_circ = QuantumCircuit.from_qasm_file(str("temp2.qasm"))
        os.remove("temp2.qasm")
        #to_dag = circuit_to_dag(to_circ)
        #return to_dag
    def function_call(self,func_list, fname_in):
        a = load(str(fname_in))
        function_dict={"not_propagation": "not_propagation",
                       "cancel_single_qubit_gates": "cancel_single_qubit_gates",
                       "cancel_two_qubit_gates" : "cancel_two_qubit_gates",
                       "merge_rotations": "merge_rotations",
                       "hadamard_reduction": "hadamard_reduction",
                       "optimize" : "optimize"}
        for i in range(len(func_list)):
            call = getattr(a, str(function_dict[func_list[i]]))
            call()
        a.write(str("temp2.qasm"))
    def rzq(self, fname_in):
        print("HIIIIIIIIIIIIIIIIIIIIIII)")
        line = []
        count = 0
        with open(str(fname_in), 'r') as f:
            data = f.readlines()
            for line in f:
                if line.startswith("rzq"):
                    line.append(count)
                    count = count+1
            print(line)
        for i in range(len(line)):   
            a = (re.findall('\d+', line[i]))[0]
            b = (re.findall('\d+', line[i]))[1]
            t= mpq(int(a), int(b))
            q = line[i].index('q[')
            t = line[i].index(']')
            fin = line[q:t+1]
            y = float(mpfr(t, 53))
            data[i] = "rz(%f) %s;\n" % (y, fin)
        with open(str(fname_in), 'w') as f:
            f.writelines(data)
