
OPENQASM 2.0;
include "qelib1.inc";

qreg q[3];
creg c[3];

barrier q;

ccx q[1], q[2], q[0];
cx  q[1], q[0];
cx  q[2], q[0];

// output

barrier q;
measure q -> c;
