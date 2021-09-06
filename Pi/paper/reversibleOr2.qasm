
OPENQASM 2.0;
include "qelib1.inc";

qreg q[3];
creg c[3];

barrier q;

cx  q[1], q[0];
x   q[1];
ccx q[1], q[2], q[0];
x   q[1];

// output

barrier q;
measure q -> c;
