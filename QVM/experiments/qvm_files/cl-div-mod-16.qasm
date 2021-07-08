OPENQASM 2.0;
include "qelib1.inc";

qreg q[49];

x q[31];
x q[28];
x q[26];
x q[24];
x q[20];
x q[19];
x q[32];
x q[48];
x q[16];
x q[17];
x q[18];
x q[19];
x q[20];
x q[21];
x q[22];
x q[23];
x q[24];
x q[25];
x q[26];
x q[27];
x q[28];
x q[29];
x q[30];
x q[31];
cx q[16], q[0];
cx q[16], q[48];
ccx q[48], q[0], q[16];
cx q[17], q[1];
cx q[17], q[16];
ccx q[16], q[1], q[17];
cx q[18], q[2];
cx q[18], q[17];
ccx q[17], q[2], q[18];
cx q[19], q[3];
cx q[19], q[18];
ccx q[18], q[3], q[19];
cx q[20], q[4];
cx q[20], q[19];
ccx q[19], q[4], q[20];
cx q[21], q[5];
cx q[21], q[20];
ccx q[20], q[5], q[21];
cx q[22], q[6];
cx q[22], q[21];
ccx q[21], q[6], q[22];
cx q[23], q[7];
cx q[23], q[22];
ccx q[22], q[7], q[23];
cx q[24], q[8];
cx q[24], q[23];
ccx q[23], q[8], q[24];
cx q[25], q[9];
cx q[25], q[24];
ccx q[24], q[9], q[25];
cx q[26], q[10];
cx q[26], q[25];
ccx q[25], q[10], q[26];
cx q[27], q[11];
cx q[27], q[26];
ccx q[26], q[11], q[27];
cx q[28], q[12];
cx q[28], q[27];
ccx q[27], q[12], q[28];
cx q[29], q[13];
cx q[29], q[28];
ccx q[28], q[13], q[29];
cx q[30], q[14];
cx q[30], q[29];
ccx q[29], q[14], q[30];
cx q[31], q[15];
cx q[31], q[30];
ccx q[30], q[15], q[31];
x q[31];
x q[32];
cx q[31], q[32];
x q[32];
x q[31];
ccx q[30], q[15], q[31];
cx q[31], q[30];
cx q[31], q[15];
ccx q[29], q[14], q[30];
cx q[30], q[29];
cx q[30], q[14];
ccx q[28], q[13], q[29];
cx q[29], q[28];
cx q[29], q[13];
ccx q[27], q[12], q[28];
cx q[28], q[27];
cx q[28], q[12];
ccx q[26], q[11], q[27];
cx q[27], q[26];
cx q[27], q[11];
ccx q[25], q[10], q[26];
cx q[26], q[25];
cx q[26], q[10];
ccx q[24], q[9], q[25];
cx q[25], q[24];
cx q[25], q[9];
ccx q[23], q[8], q[24];
cx q[24], q[23];
cx q[24], q[8];
ccx q[22], q[7], q[23];
cx q[23], q[22];
cx q[23], q[7];
ccx q[21], q[6], q[22];
cx q[22], q[21];
cx q[22], q[6];
ccx q[20], q[5], q[21];
cx q[21], q[20];
cx q[21], q[5];
ccx q[19], q[4], q[20];
cx q[20], q[19];
cx q[20], q[4];
ccx q[18], q[3], q[19];
cx q[19], q[18];
cx q[19], q[3];
ccx q[17], q[2], q[18];
cx q[18], q[17];
cx q[18], q[2];
ccx q[16], q[1], q[17];
cx q[17], q[16];
cx q[17], q[1];
ccx q[48], q[0], q[16];
cx q[16], q[48];
cx q[16], q[0];
x q[31];
x q[30];
x q[29];
x q[28];
x q[27];
x q[26];
x q[25];
x q[24];
x q[23];
x q[22];
x q[21];
x q[20];
x q[19];
x q[18];
x q[17];
x q[16];
x q[48];
cx q[32], q[48];
cx q[32], q[16];
cx q[32], q[17];
cx q[32], q[18];
cx q[32], q[19];
cx q[32], q[20];
cx q[32], q[21];
cx q[32], q[22];
cx q[32], q[23];
cx q[32], q[24];
cx q[32], q[25];
cx q[32], q[26];
cx q[32], q[27];
cx q[32], q[28];
cx q[32], q[29];
cx q[32], q[30];
cx q[32], q[31];
ccx q[32], q[16], q[0];
ccx q[32], q[16], q[48];
u3(0.785398,0.000000,0.000000) q[16];
cx q[32], q[16];
u3(-0.785398,0.000000,0.000000) q[16];
ccx q[32], q[0], q[16];
u1(-0.392699) q[32];
u1(-0.392699) q[16];
cx q[32], q[16];
u1(0.392699) q[16];
cx q[32], q[16];
ccx q[32], q[48], q[16];
u1(0.392699) q[32];
u1(0.392699) q[16];
cx q[32], q[16];
u1(-0.392699) q[16];
cx q[32], q[16];
ccx q[32], q[0], q[16];
u1(-0.392699) q[32];
u1(-0.392699) q[16];
cx q[32], q[16];
u1(0.392699) q[16];
cx q[32], q[16];
ccx q[32], q[48], q[16];
ccx q[32], q[48], q[0];
u1(-0.392699) q[32];
u1(-0.392699) q[0];
cx q[32], q[0];
u1(0.392699) q[0];
cx q[32], q[0];
ccx q[32], q[48], q[0];
u1(0.392699) q[32];
u1(0.392699) q[48];
cx q[32], q[48];
u1(-0.392699) q[48];
cx q[32], q[48];
u1(0.392699) q[32];
u1(0.392699) q[0];
cx q[32], q[0];
u1(-0.392699) q[0];
cx q[32], q[0];
u1(0.392699) q[32];
u1(0.392699) q[16];
cx q[32], q[16];
u1(-0.392699) q[16];
cx q[32], q[16];
u3(0.785398,0.000000,0.000000) q[16];
cx q[32], q[16];
u3(-0.785398,0.000000,0.000000) q[16];
ccx q[32], q[17], q[1];
ccx q[32], q[17], q[16];
u3(0.785398,0.000000,0.000000) q[17];
cx q[32], q[17];
u3(-0.785398,0.000000,0.000000) q[17];
ccx q[32], q[1], q[17];
u1(-0.392699) q[32];
u1(-0.392699) q[17];
cx q[32], q[17];
u1(0.392699) q[17];
cx q[32], q[17];
ccx q[32], q[16], q[17];
u1(0.392699) q[32];
u1(0.392699) q[17];
cx q[32], q[17];
u1(-0.392699) q[17];
cx q[32], q[17];
ccx q[32], q[1], q[17];
u1(-0.392699) q[32];
u1(-0.392699) q[17];
cx q[32], q[17];
u1(0.392699) q[17];
cx q[32], q[17];
ccx q[32], q[16], q[17];
ccx q[32], q[16], q[1];
u1(-0.392699) q[32];
u1(-0.392699) q[1];
cx q[32], q[1];
u1(0.392699) q[1];
cx q[32], q[1];
ccx q[32], q[16], q[1];
u1(0.392699) q[32];
u1(0.392699) q[16];
cx q[32], q[16];
u1(-0.392699) q[16];
cx q[32], q[16];
u1(0.392699) q[32];
u1(0.392699) q[1];
cx q[32], q[1];
u1(-0.392699) q[1];
cx q[32], q[1];
u1(0.392699) q[32];
u1(0.392699) q[17];
cx q[32], q[17];
u1(-0.392699) q[17];
cx q[32], q[17];
u3(0.785398,0.000000,0.000000) q[17];
cx q[32], q[17];
u3(-0.785398,0.000000,0.000000) q[17];
ccx q[32], q[18], q[2];
ccx q[32], q[18], q[17];
u3(0.785398,0.000000,0.000000) q[18];
cx q[32], q[18];
u3(-0.785398,0.000000,0.000000) q[18];
ccx q[32], q[2], q[18];
u1(-0.392699) q[32];
u1(-0.392699) q[18];
cx q[32], q[18];
u1(0.392699) q[18];
cx q[32], q[18];
ccx q[32], q[17], q[18];
u1(0.392699) q[32];
u1(0.392699) q[18];
cx q[32], q[18];
u1(-0.392699) q[18];
cx q[32], q[18];
ccx q[32], q[2], q[18];
u1(-0.392699) q[32];
u1(-0.392699) q[18];
cx q[32], q[18];
u1(0.392699) q[18];
cx q[32], q[18];
ccx q[32], q[17], q[18];
ccx q[32], q[17], q[2];
u1(-0.392699) q[32];
u1(-0.392699) q[2];
cx q[32], q[2];
u1(0.392699) q[2];
cx q[32], q[2];
ccx q[32], q[17], q[2];
u1(0.392699) q[32];
u1(0.392699) q[17];
cx q[32], q[17];
u1(-0.392699) q[17];
cx q[32], q[17];
u1(0.392699) q[32];
u1(0.392699) q[2];
cx q[32], q[2];
u1(-0.392699) q[2];
cx q[32], q[2];
u1(0.392699) q[32];
u1(0.392699) q[18];
cx q[32], q[18];
u1(-0.392699) q[18];
cx q[32], q[18];
u3(0.785398,0.000000,0.000000) q[18];
cx q[32], q[18];
u3(-0.785398,0.000000,0.000000) q[18];
ccx q[32], q[19], q[3];
ccx q[32], q[19], q[18];
u3(0.785398,0.000000,0.000000) q[19];
cx q[32], q[19];
u3(-0.785398,0.000000,0.000000) q[19];
ccx q[32], q[3], q[19];
u1(-0.392699) q[32];
u1(-0.392699) q[19];
cx q[32], q[19];
u1(0.392699) q[19];
cx q[32], q[19];
ccx q[32], q[18], q[19];
u1(0.392699) q[32];
u1(0.392699) q[19];
cx q[32], q[19];
u1(-0.392699) q[19];
cx q[32], q[19];
ccx q[32], q[3], q[19];
u1(-0.392699) q[32];
u1(-0.392699) q[19];
cx q[32], q[19];
u1(0.392699) q[19];
cx q[32], q[19];
ccx q[32], q[18], q[19];
ccx q[32], q[18], q[3];
u1(-0.392699) q[32];
u1(-0.392699) q[3];
cx q[32], q[3];
u1(0.392699) q[3];
cx q[32], q[3];
ccx q[32], q[18], q[3];
u1(0.392699) q[32];
u1(0.392699) q[18];
cx q[32], q[18];
u1(-0.392699) q[18];
cx q[32], q[18];
u1(0.392699) q[32];
u1(0.392699) q[3];
cx q[32], q[3];
u1(-0.392699) q[3];
cx q[32], q[3];
u1(0.392699) q[32];
u1(0.392699) q[19];
cx q[32], q[19];
u1(-0.392699) q[19];
cx q[32], q[19];
u3(0.785398,0.000000,0.000000) q[19];
cx q[32], q[19];
u3(-0.785398,0.000000,0.000000) q[19];
ccx q[32], q[20], q[4];
ccx q[32], q[20], q[19];
u3(0.785398,0.000000,0.000000) q[20];
cx q[32], q[20];
u3(-0.785398,0.000000,0.000000) q[20];
ccx q[32], q[4], q[20];
u1(-0.392699) q[32];
u1(-0.392699) q[20];
cx q[32], q[20];
u1(0.392699) q[20];
cx q[32], q[20];
ccx q[32], q[19], q[20];
u1(0.392699) q[32];
u1(0.392699) q[20];
cx q[32], q[20];
u1(-0.392699) q[20];
cx q[32], q[20];
ccx q[32], q[4], q[20];
u1(-0.392699) q[32];
u1(-0.392699) q[20];
cx q[32], q[20];
u1(0.392699) q[20];
cx q[32], q[20];
ccx q[32], q[19], q[20];
ccx q[32], q[19], q[4];
u1(-0.392699) q[32];
u1(-0.392699) q[4];
cx q[32], q[4];
u1(0.392699) q[4];
cx q[32], q[4];
ccx q[32], q[19], q[4];
u1(0.392699) q[32];
u1(0.392699) q[19];
cx q[32], q[19];
u1(-0.392699) q[19];
cx q[32], q[19];
u1(0.392699) q[32];
u1(0.392699) q[4];
cx q[32], q[4];
u1(-0.392699) q[4];
cx q[32], q[4];
u1(0.392699) q[32];
u1(0.392699) q[20];
cx q[32], q[20];
u1(-0.392699) q[20];
cx q[32], q[20];
u3(0.785398,0.000000,0.000000) q[20];
cx q[32], q[20];
u3(-0.785398,0.000000,0.000000) q[20];
ccx q[32], q[21], q[5];
ccx q[32], q[21], q[20];
u3(0.785398,0.000000,0.000000) q[21];
cx q[32], q[21];
u3(-0.785398,0.000000,0.000000) q[21];
ccx q[32], q[5], q[21];
u1(-0.392699) q[32];
u1(-0.392699) q[21];
cx q[32], q[21];
u1(0.392699) q[21];
cx q[32], q[21];
ccx q[32], q[20], q[21];
u1(0.392699) q[32];
u1(0.392699) q[21];
cx q[32], q[21];
u1(-0.392699) q[21];
cx q[32], q[21];
ccx q[32], q[5], q[21];
u1(-0.392699) q[32];
u1(-0.392699) q[21];
cx q[32], q[21];
u1(0.392699) q[21];
cx q[32], q[21];
ccx q[32], q[20], q[21];
ccx q[32], q[20], q[5];
u1(-0.392699) q[32];
u1(-0.392699) q[5];
cx q[32], q[5];
u1(0.392699) q[5];
cx q[32], q[5];
ccx q[32], q[20], q[5];
u1(0.392699) q[32];
u1(0.392699) q[20];
cx q[32], q[20];
u1(-0.392699) q[20];
cx q[32], q[20];
u1(0.392699) q[32];
u1(0.392699) q[5];
cx q[32], q[5];
u1(-0.392699) q[5];
cx q[32], q[5];
u1(0.392699) q[32];
u1(0.392699) q[21];
cx q[32], q[21];
u1(-0.392699) q[21];
cx q[32], q[21];
u3(0.785398,0.000000,0.000000) q[21];
cx q[32], q[21];
u3(-0.785398,0.000000,0.000000) q[21];
ccx q[32], q[22], q[6];
ccx q[32], q[22], q[21];
u3(0.785398,0.000000,0.000000) q[22];
cx q[32], q[22];
u3(-0.785398,0.000000,0.000000) q[22];
ccx q[32], q[6], q[22];
u1(-0.392699) q[32];
u1(-0.392699) q[22];
cx q[32], q[22];
u1(0.392699) q[22];
cx q[32], q[22];
ccx q[32], q[21], q[22];
u1(0.392699) q[32];
u1(0.392699) q[22];
cx q[32], q[22];
u1(-0.392699) q[22];
cx q[32], q[22];
ccx q[32], q[6], q[22];
u1(-0.392699) q[32];
u1(-0.392699) q[22];
cx q[32], q[22];
u1(0.392699) q[22];
cx q[32], q[22];
ccx q[32], q[21], q[22];
ccx q[32], q[21], q[6];
u1(-0.392699) q[32];
u1(-0.392699) q[6];
cx q[32], q[6];
u1(0.392699) q[6];
cx q[32], q[6];
ccx q[32], q[21], q[6];
u1(0.392699) q[32];
u1(0.392699) q[21];
cx q[32], q[21];
u1(-0.392699) q[21];
cx q[32], q[21];
u1(0.392699) q[32];
u1(0.392699) q[6];
cx q[32], q[6];
u1(-0.392699) q[6];
cx q[32], q[6];
u1(0.392699) q[32];
u1(0.392699) q[22];
cx q[32], q[22];
u1(-0.392699) q[22];
cx q[32], q[22];
u3(0.785398,0.000000,0.000000) q[22];
cx q[32], q[22];
u3(-0.785398,0.000000,0.000000) q[22];
ccx q[32], q[23], q[7];
ccx q[32], q[23], q[22];
u3(0.785398,0.000000,0.000000) q[23];
cx q[32], q[23];
u3(-0.785398,0.000000,0.000000) q[23];
ccx q[32], q[7], q[23];
u1(-0.392699) q[32];
u1(-0.392699) q[23];
cx q[32], q[23];
u1(0.392699) q[23];
cx q[32], q[23];
ccx q[32], q[22], q[23];
u1(0.392699) q[32];
u1(0.392699) q[23];
cx q[32], q[23];
u1(-0.392699) q[23];
cx q[32], q[23];
ccx q[32], q[7], q[23];
u1(-0.392699) q[32];
u1(-0.392699) q[23];
cx q[32], q[23];
u1(0.392699) q[23];
cx q[32], q[23];
ccx q[32], q[22], q[23];
ccx q[32], q[22], q[7];
u1(-0.392699) q[32];
u1(-0.392699) q[7];
cx q[32], q[7];
u1(0.392699) q[7];
cx q[32], q[7];
ccx q[32], q[22], q[7];
u1(0.392699) q[32];
u1(0.392699) q[22];
cx q[32], q[22];
u1(-0.392699) q[22];
cx q[32], q[22];
u1(0.392699) q[32];
u1(0.392699) q[7];
cx q[32], q[7];
u1(-0.392699) q[7];
cx q[32], q[7];
u1(0.392699) q[32];
u1(0.392699) q[23];
cx q[32], q[23];
u1(-0.392699) q[23];
cx q[32], q[23];
u3(0.785398,0.000000,0.000000) q[23];
cx q[32], q[23];
u3(-0.785398,0.000000,0.000000) q[23];
ccx q[32], q[24], q[8];
ccx q[32], q[24], q[23];
u3(0.785398,0.000000,0.000000) q[24];
cx q[32], q[24];
u3(-0.785398,0.000000,0.000000) q[24];
ccx q[32], q[8], q[24];
u1(-0.392699) q[32];
u1(-0.392699) q[24];
cx q[32], q[24];
u1(0.392699) q[24];
cx q[32], q[24];
ccx q[32], q[23], q[24];
u1(0.392699) q[32];
u1(0.392699) q[24];
cx q[32], q[24];
u1(-0.392699) q[24];
cx q[32], q[24];
ccx q[32], q[8], q[24];
u1(-0.392699) q[32];
u1(-0.392699) q[24];
cx q[32], q[24];
u1(0.392699) q[24];
cx q[32], q[24];
ccx q[32], q[23], q[24];
ccx q[32], q[23], q[8];
u1(-0.392699) q[32];
u1(-0.392699) q[8];
cx q[32], q[8];
u1(0.392699) q[8];
cx q[32], q[8];
ccx q[32], q[23], q[8];
u1(0.392699) q[32];
u1(0.392699) q[23];
cx q[32], q[23];
u1(-0.392699) q[23];
cx q[32], q[23];
u1(0.392699) q[32];
u1(0.392699) q[8];
cx q[32], q[8];
u1(-0.392699) q[8];
cx q[32], q[8];
u1(0.392699) q[32];
u1(0.392699) q[24];
cx q[32], q[24];
u1(-0.392699) q[24];
cx q[32], q[24];
u3(0.785398,0.000000,0.000000) q[24];
cx q[32], q[24];
u3(-0.785398,0.000000,0.000000) q[24];
ccx q[32], q[25], q[9];
ccx q[32], q[25], q[24];
u3(0.785398,0.000000,0.000000) q[25];
cx q[32], q[25];
u3(-0.785398,0.000000,0.000000) q[25];
ccx q[32], q[9], q[25];
u1(-0.392699) q[32];
u1(-0.392699) q[25];
cx q[32], q[25];
u1(0.392699) q[25];
cx q[32], q[25];
ccx q[32], q[24], q[25];
u1(0.392699) q[32];
u1(0.392699) q[25];
cx q[32], q[25];
u1(-0.392699) q[25];
cx q[32], q[25];
ccx q[32], q[9], q[25];
u1(-0.392699) q[32];
u1(-0.392699) q[25];
cx q[32], q[25];
u1(0.392699) q[25];
cx q[32], q[25];
ccx q[32], q[24], q[25];
ccx q[32], q[24], q[9];
u1(-0.392699) q[32];
u1(-0.392699) q[9];
cx q[32], q[9];
u1(0.392699) q[9];
cx q[32], q[9];
ccx q[32], q[24], q[9];
u1(0.392699) q[32];
u1(0.392699) q[24];
cx q[32], q[24];
u1(-0.392699) q[24];
cx q[32], q[24];
u1(0.392699) q[32];
u1(0.392699) q[9];
cx q[32], q[9];
u1(-0.392699) q[9];
cx q[32], q[9];
u1(0.392699) q[32];
u1(0.392699) q[25];
cx q[32], q[25];
u1(-0.392699) q[25];
cx q[32], q[25];
u3(0.785398,0.000000,0.000000) q[25];
cx q[32], q[25];
u3(-0.785398,0.000000,0.000000) q[25];
ccx q[32], q[26], q[10];
ccx q[32], q[26], q[25];
u3(0.785398,0.000000,0.000000) q[26];
cx q[32], q[26];
u3(-0.785398,0.000000,0.000000) q[26];
ccx q[32], q[10], q[26];
u1(-0.392699) q[32];
u1(-0.392699) q[26];
cx q[32], q[26];
u1(0.392699) q[26];
cx q[32], q[26];
ccx q[32], q[25], q[26];
u1(0.392699) q[32];
u1(0.392699) q[26];
cx q[32], q[26];
u1(-0.392699) q[26];
cx q[32], q[26];
ccx q[32], q[10], q[26];
u1(-0.392699) q[32];
u1(-0.392699) q[26];
cx q[32], q[26];
u1(0.392699) q[26];
cx q[32], q[26];
ccx q[32], q[25], q[26];
ccx q[32], q[25], q[10];
u1(-0.392699) q[32];
u1(-0.392699) q[10];
cx q[32], q[10];
u1(0.392699) q[10];
cx q[32], q[10];
ccx q[32], q[25], q[10];
u1(0.392699) q[32];
u1(0.392699) q[25];
cx q[32], q[25];
u1(-0.392699) q[25];
cx q[32], q[25];
u1(0.392699) q[32];
u1(0.392699) q[10];
cx q[32], q[10];
u1(-0.392699) q[10];
cx q[32], q[10];
u1(0.392699) q[32];
u1(0.392699) q[26];
cx q[32], q[26];
u1(-0.392699) q[26];
cx q[32], q[26];
u3(0.785398,0.000000,0.000000) q[26];
cx q[32], q[26];
u3(-0.785398,0.000000,0.000000) q[26];
ccx q[32], q[27], q[11];
ccx q[32], q[27], q[26];
u3(0.785398,0.000000,0.000000) q[27];
cx q[32], q[27];
u3(-0.785398,0.000000,0.000000) q[27];
ccx q[32], q[11], q[27];
u1(-0.392699) q[32];
u1(-0.392699) q[27];
cx q[32], q[27];
u1(0.392699) q[27];
cx q[32], q[27];
ccx q[32], q[26], q[27];
u1(0.392699) q[32];
u1(0.392699) q[27];
cx q[32], q[27];
u1(-0.392699) q[27];
cx q[32], q[27];
ccx q[32], q[11], q[27];
u1(-0.392699) q[32];
u1(-0.392699) q[27];
cx q[32], q[27];
u1(0.392699) q[27];
cx q[32], q[27];
ccx q[32], q[26], q[27];
ccx q[32], q[26], q[11];
u1(-0.392699) q[32];
u1(-0.392699) q[11];
cx q[32], q[11];
u1(0.392699) q[11];
cx q[32], q[11];
ccx q[32], q[26], q[11];
u1(0.392699) q[32];
u1(0.392699) q[26];
cx q[32], q[26];
u1(-0.392699) q[26];
cx q[32], q[26];
u1(0.392699) q[32];
u1(0.392699) q[11];
cx q[32], q[11];
u1(-0.392699) q[11];
cx q[32], q[11];
u1(0.392699) q[32];
u1(0.392699) q[27];
cx q[32], q[27];
u1(-0.392699) q[27];
cx q[32], q[27];
u3(0.785398,0.000000,0.000000) q[27];
cx q[32], q[27];
u3(-0.785398,0.000000,0.000000) q[27];
ccx q[32], q[28], q[12];
ccx q[32], q[28], q[27];
u3(0.785398,0.000000,0.000000) q[28];
cx q[32], q[28];
u3(-0.785398,0.000000,0.000000) q[28];
ccx q[32], q[12], q[28];
u1(-0.392699) q[32];
u1(-0.392699) q[28];
cx q[32], q[28];
u1(0.392699) q[28];
cx q[32], q[28];
ccx q[32], q[27], q[28];
u1(0.392699) q[32];
u1(0.392699) q[28];
cx q[32], q[28];
u1(-0.392699) q[28];
cx q[32], q[28];
ccx q[32], q[12], q[28];
u1(-0.392699) q[32];
u1(-0.392699) q[28];
cx q[32], q[28];
u1(0.392699) q[28];
cx q[32], q[28];
ccx q[32], q[27], q[28];
ccx q[32], q[27], q[12];
u1(-0.392699) q[32];
u1(-0.392699) q[12];
cx q[32], q[12];
u1(0.392699) q[12];
cx q[32], q[12];
ccx q[32], q[27], q[12];
u1(0.392699) q[32];
u1(0.392699) q[27];
cx q[32], q[27];
u1(-0.392699) q[27];
cx q[32], q[27];
u1(0.392699) q[32];
u1(0.392699) q[12];
cx q[32], q[12];
u1(-0.392699) q[12];
cx q[32], q[12];
u1(0.392699) q[32];
u1(0.392699) q[28];
cx q[32], q[28];
u1(-0.392699) q[28];
cx q[32], q[28];
u3(0.785398,0.000000,0.000000) q[28];
cx q[32], q[28];
u3(-0.785398,0.000000,0.000000) q[28];
ccx q[32], q[29], q[13];
ccx q[32], q[29], q[28];
u3(0.785398,0.000000,0.000000) q[29];
cx q[32], q[29];
u3(-0.785398,0.000000,0.000000) q[29];
ccx q[32], q[13], q[29];
u1(-0.392699) q[32];
u1(-0.392699) q[29];
cx q[32], q[29];
u1(0.392699) q[29];
cx q[32], q[29];
ccx q[32], q[28], q[29];
u1(0.392699) q[32];
u1(0.392699) q[29];
cx q[32], q[29];
u1(-0.392699) q[29];
cx q[32], q[29];
ccx q[32], q[13], q[29];
u1(-0.392699) q[32];
u1(-0.392699) q[29];
cx q[32], q[29];
u1(0.392699) q[29];
cx q[32], q[29];
ccx q[32], q[28], q[29];
ccx q[32], q[28], q[13];
u1(-0.392699) q[32];
u1(-0.392699) q[13];
cx q[32], q[13];
u1(0.392699) q[13];
cx q[32], q[13];
ccx q[32], q[28], q[13];
u1(0.392699) q[32];
u1(0.392699) q[28];
cx q[32], q[28];
u1(-0.392699) q[28];
cx q[32], q[28];
u1(0.392699) q[32];
u1(0.392699) q[13];
cx q[32], q[13];
u1(-0.392699) q[13];
cx q[32], q[13];
u1(0.392699) q[32];
u1(0.392699) q[29];
cx q[32], q[29];
u1(-0.392699) q[29];
cx q[32], q[29];
u3(0.785398,0.000000,0.000000) q[29];
cx q[32], q[29];
u3(-0.785398,0.000000,0.000000) q[29];
ccx q[32], q[30], q[14];
ccx q[32], q[30], q[29];
u3(0.785398,0.000000,0.000000) q[30];
cx q[32], q[30];
u3(-0.785398,0.000000,0.000000) q[30];
ccx q[32], q[14], q[30];
u1(-0.392699) q[32];
u1(-0.392699) q[30];
cx q[32], q[30];
u1(0.392699) q[30];
cx q[32], q[30];
ccx q[32], q[29], q[30];
u1(0.392699) q[32];
u1(0.392699) q[30];
cx q[32], q[30];
u1(-0.392699) q[30];
cx q[32], q[30];
ccx q[32], q[14], q[30];
u1(-0.392699) q[32];
u1(-0.392699) q[30];
cx q[32], q[30];
u1(0.392699) q[30];
cx q[32], q[30];
ccx q[32], q[29], q[30];
ccx q[32], q[29], q[14];
u1(-0.392699) q[32];
u1(-0.392699) q[14];
cx q[32], q[14];
u1(0.392699) q[14];
cx q[32], q[14];
ccx q[32], q[29], q[14];
u1(0.392699) q[32];
u1(0.392699) q[29];
cx q[32], q[29];
u1(-0.392699) q[29];
cx q[32], q[29];
u1(0.392699) q[32];
u1(0.392699) q[14];
cx q[32], q[14];
u1(-0.392699) q[14];
cx q[32], q[14];
u1(0.392699) q[32];
u1(0.392699) q[30];
cx q[32], q[30];
u1(-0.392699) q[30];
cx q[32], q[30];
u3(0.785398,0.000000,0.000000) q[30];
cx q[32], q[30];
u3(-0.785398,0.000000,0.000000) q[30];
ccx q[32], q[31], q[15];
ccx q[32], q[31], q[30];
u3(0.785398,0.000000,0.000000) q[31];
cx q[32], q[31];
u3(-0.785398,0.000000,0.000000) q[31];
ccx q[32], q[15], q[31];
u1(-0.392699) q[32];
u1(-0.392699) q[31];
cx q[32], q[31];
u1(0.392699) q[31];
cx q[32], q[31];
ccx q[32], q[30], q[31];
u1(0.392699) q[32];
u1(0.392699) q[31];
cx q[32], q[31];
u1(-0.392699) q[31];
cx q[32], q[31];
ccx q[32], q[15], q[31];
u1(-0.392699) q[32];
u1(-0.392699) q[31];
cx q[32], q[31];
u1(0.392699) q[31];
cx q[32], q[31];
ccx q[32], q[30], q[31];
ccx q[32], q[30], q[15];
u1(-0.392699) q[32];
u1(-0.392699) q[15];
cx q[32], q[15];
u1(0.392699) q[15];
cx q[32], q[15];
ccx q[32], q[30], q[15];
u1(0.392699) q[32];
u1(0.392699) q[30];
cx q[32], q[30];
u1(-0.392699) q[30];
cx q[32], q[30];
u1(0.392699) q[32];
u1(0.392699) q[15];
cx q[32], q[15];
u1(-0.392699) q[15];
cx q[32], q[15];
u1(0.392699) q[32];
u1(0.392699) q[31];
cx q[32], q[31];
u1(-0.392699) q[31];
cx q[32], q[31];
u3(0.785398,0.000000,0.000000) q[31];
cx q[32], q[31];
u3(-0.785398,0.000000,0.000000) q[31];
u3(0.785398,0.000000,0.000000) q[31];
cx q[32], q[31];
u3(-0.785398,0.000000,0.000000) q[31];
ccx q[32], q[15], q[31];
u1(-0.392699) q[32];
u1(-0.392699) q[31];
cx q[32], q[31];
u1(0.392699) q[31];
cx q[32], q[31];
ccx q[32], q[30], q[31];
u1(0.392699) q[32];
u1(0.392699) q[31];
cx q[32], q[31];
u1(-0.392699) q[31];
cx q[32], q[31];
ccx q[32], q[15], q[31];
u1(-0.392699) q[32];
u1(-0.392699) q[31];
cx q[32], q[31];
u1(0.392699) q[31];
cx q[32], q[31];
ccx q[32], q[30], q[31];
ccx q[32], q[30], q[15];
u1(-0.392699) q[32];
u1(-0.392699) q[15];
cx q[32], q[15];
u1(0.392699) q[15];
cx q[32], q[15];
ccx q[32], q[30], q[15];
u1(0.392699) q[32];
u1(0.392699) q[30];
cx q[32], q[30];
u1(-0.392699) q[30];
cx q[32], q[30];
u1(0.392699) q[32];
u1(0.392699) q[15];
cx q[32], q[15];
u1(-0.392699) q[15];
cx q[32], q[15];
u1(0.392699) q[32];
u1(0.392699) q[31];
cx q[32], q[31];
u1(-0.392699) q[31];
cx q[32], q[31];
u3(0.785398,0.000000,0.000000) q[31];
cx q[32], q[31];
u3(-0.785398,0.000000,0.000000) q[31];
ccx q[32], q[31], q[30];
ccx q[32], q[30], q[15];
u3(0.785398,0.000000,0.000000) q[30];
cx q[32], q[30];
u3(-0.785398,0.000000,0.000000) q[30];
ccx q[32], q[14], q[30];
u1(-0.392699) q[32];
u1(-0.392699) q[30];
cx q[32], q[30];
u1(0.392699) q[30];
cx q[32], q[30];
ccx q[32], q[29], q[30];
u1(0.392699) q[32];
u1(0.392699) q[30];
cx q[32], q[30];
u1(-0.392699) q[30];
cx q[32], q[30];
ccx q[32], q[14], q[30];
u1(-0.392699) q[32];
u1(-0.392699) q[30];
cx q[32], q[30];
u1(0.392699) q[30];
cx q[32], q[30];
ccx q[32], q[29], q[30];
ccx q[32], q[29], q[14];
u1(-0.392699) q[32];
u1(-0.392699) q[14];
cx q[32], q[14];
u1(0.392699) q[14];
cx q[32], q[14];
ccx q[32], q[29], q[14];
u1(0.392699) q[32];
u1(0.392699) q[29];
cx q[32], q[29];
u1(-0.392699) q[29];
cx q[32], q[29];
u1(0.392699) q[32];
u1(0.392699) q[14];
cx q[32], q[14];
u1(-0.392699) q[14];
cx q[32], q[14];
u1(0.392699) q[32];
u1(0.392699) q[30];
cx q[32], q[30];
u1(-0.392699) q[30];
cx q[32], q[30];
u3(0.785398,0.000000,0.000000) q[30];
cx q[32], q[30];
u3(-0.785398,0.000000,0.000000) q[30];
ccx q[32], q[30], q[29];
ccx q[32], q[29], q[14];
u3(0.785398,0.000000,0.000000) q[29];
cx q[32], q[29];
u3(-0.785398,0.000000,0.000000) q[29];
ccx q[32], q[13], q[29];
u1(-0.392699) q[32];
u1(-0.392699) q[29];
cx q[32], q[29];
u1(0.392699) q[29];
cx q[32], q[29];
ccx q[32], q[28], q[29];
u1(0.392699) q[32];
u1(0.392699) q[29];
cx q[32], q[29];
u1(-0.392699) q[29];
cx q[32], q[29];
ccx q[32], q[13], q[29];
u1(-0.392699) q[32];
u1(-0.392699) q[29];
cx q[32], q[29];
u1(0.392699) q[29];
cx q[32], q[29];
ccx q[32], q[28], q[29];
ccx q[32], q[28], q[13];
u1(-0.392699) q[32];
u1(-0.392699) q[13];
cx q[32], q[13];
u1(0.392699) q[13];
cx q[32], q[13];
ccx q[32], q[28], q[13];
u1(0.392699) q[32];
u1(0.392699) q[28];
cx q[32], q[28];
u1(-0.392699) q[28];
cx q[32], q[28];
u1(0.392699) q[32];
u1(0.392699) q[13];
cx q[32], q[13];
u1(-0.392699) q[13];
cx q[32], q[13];
u1(0.392699) q[32];
u1(0.392699) q[29];
cx q[32], q[29];
u1(-0.392699) q[29];
cx q[32], q[29];
u3(0.785398,0.000000,0.000000) q[29];
cx q[32], q[29];
u3(-0.785398,0.000000,0.000000) q[29];
ccx q[32], q[29], q[28];
ccx q[32], q[28], q[13];
u3(0.785398,0.000000,0.000000) q[28];
cx q[32], q[28];
u3(-0.785398,0.000000,0.000000) q[28];
ccx q[32], q[12], q[28];
u1(-0.392699) q[32];
u1(-0.392699) q[28];
cx q[32], q[28];
u1(0.392699) q[28];
cx q[32], q[28];
ccx q[32], q[27], q[28];
u1(0.392699) q[32];
u1(0.392699) q[28];
cx q[32], q[28];
u1(-0.392699) q[28];
cx q[32], q[28];
ccx q[32], q[12], q[28];
u1(-0.392699) q[32];
u1(-0.392699) q[28];
cx q[32], q[28];
u1(0.392699) q[28];
cx q[32], q[28];
ccx q[32], q[27], q[28];
ccx q[32], q[27], q[12];
u1(-0.392699) q[32];
u1(-0.392699) q[12];
cx q[32], q[12];
u1(0.392699) q[12];
cx q[32], q[12];
ccx q[32], q[27], q[12];
u1(0.392699) q[32];
u1(0.392699) q[27];
cx q[32], q[27];
u1(-0.392699) q[27];
cx q[32], q[27];
u1(0.392699) q[32];
u1(0.392699) q[12];
cx q[32], q[12];
u1(-0.392699) q[12];
cx q[32], q[12];
u1(0.392699) q[32];
u1(0.392699) q[28];
cx q[32], q[28];
u1(-0.392699) q[28];
cx q[32], q[28];
u3(0.785398,0.000000,0.000000) q[28];
cx q[32], q[28];
u3(-0.785398,0.000000,0.000000) q[28];
ccx q[32], q[28], q[27];
ccx q[32], q[27], q[12];
u3(0.785398,0.000000,0.000000) q[27];
cx q[32], q[27];
u3(-0.785398,0.000000,0.000000) q[27];
ccx q[32], q[11], q[27];
u1(-0.392699) q[32];
u1(-0.392699) q[27];
cx q[32], q[27];
u1(0.392699) q[27];
cx q[32], q[27];
ccx q[32], q[26], q[27];
u1(0.392699) q[32];
u1(0.392699) q[27];
cx q[32], q[27];
u1(-0.392699) q[27];
cx q[32], q[27];
ccx q[32], q[11], q[27];
u1(-0.392699) q[32];
u1(-0.392699) q[27];
cx q[32], q[27];
u1(0.392699) q[27];
cx q[32], q[27];
ccx q[32], q[26], q[27];
ccx q[32], q[26], q[11];
u1(-0.392699) q[32];
u1(-0.392699) q[11];
cx q[32], q[11];
u1(0.392699) q[11];
cx q[32], q[11];
ccx q[32], q[26], q[11];
u1(0.392699) q[32];
u1(0.392699) q[26];
cx q[32], q[26];
u1(-0.392699) q[26];
cx q[32], q[26];
u1(0.392699) q[32];
u1(0.392699) q[11];
cx q[32], q[11];
u1(-0.392699) q[11];
cx q[32], q[11];
u1(0.392699) q[32];
u1(0.392699) q[27];
cx q[32], q[27];
u1(-0.392699) q[27];
cx q[32], q[27];
u3(0.785398,0.000000,0.000000) q[27];
cx q[32], q[27];
u3(-0.785398,0.000000,0.000000) q[27];
ccx q[32], q[27], q[26];
ccx q[32], q[26], q[11];
u3(0.785398,0.000000,0.000000) q[26];
cx q[32], q[26];
u3(-0.785398,0.000000,0.000000) q[26];
ccx q[32], q[10], q[26];
u1(-0.392699) q[32];
u1(-0.392699) q[26];
cx q[32], q[26];
u1(0.392699) q[26];
cx q[32], q[26];
ccx q[32], q[25], q[26];
u1(0.392699) q[32];
u1(0.392699) q[26];
cx q[32], q[26];
u1(-0.392699) q[26];
cx q[32], q[26];
ccx q[32], q[10], q[26];
u1(-0.392699) q[32];
u1(-0.392699) q[26];
cx q[32], q[26];
u1(0.392699) q[26];
cx q[32], q[26];
ccx q[32], q[25], q[26];
ccx q[32], q[25], q[10];
u1(-0.392699) q[32];
u1(-0.392699) q[10];
cx q[32], q[10];
u1(0.392699) q[10];
cx q[32], q[10];
ccx q[32], q[25], q[10];
u1(0.392699) q[32];
u1(0.392699) q[25];
cx q[32], q[25];
u1(-0.392699) q[25];
cx q[32], q[25];
u1(0.392699) q[32];
u1(0.392699) q[10];
cx q[32], q[10];
u1(-0.392699) q[10];
cx q[32], q[10];
u1(0.392699) q[32];
u1(0.392699) q[26];
cx q[32], q[26];
u1(-0.392699) q[26];
cx q[32], q[26];
u3(0.785398,0.000000,0.000000) q[26];
cx q[32], q[26];
u3(-0.785398,0.000000,0.000000) q[26];
ccx q[32], q[26], q[25];
ccx q[32], q[25], q[10];
u3(0.785398,0.000000,0.000000) q[25];
cx q[32], q[25];
u3(-0.785398,0.000000,0.000000) q[25];
ccx q[32], q[9], q[25];
u1(-0.392699) q[32];
u1(-0.392699) q[25];
cx q[32], q[25];
u1(0.392699) q[25];
cx q[32], q[25];
ccx q[32], q[24], q[25];
u1(0.392699) q[32];
u1(0.392699) q[25];
cx q[32], q[25];
u1(-0.392699) q[25];
cx q[32], q[25];
ccx q[32], q[9], q[25];
u1(-0.392699) q[32];
u1(-0.392699) q[25];
cx q[32], q[25];
u1(0.392699) q[25];
cx q[32], q[25];
ccx q[32], q[24], q[25];
ccx q[32], q[24], q[9];
u1(-0.392699) q[32];
u1(-0.392699) q[9];
cx q[32], q[9];
u1(0.392699) q[9];
cx q[32], q[9];
ccx q[32], q[24], q[9];
u1(0.392699) q[32];
u1(0.392699) q[24];
cx q[32], q[24];
u1(-0.392699) q[24];
cx q[32], q[24];
u1(0.392699) q[32];
u1(0.392699) q[9];
cx q[32], q[9];
u1(-0.392699) q[9];
cx q[32], q[9];
u1(0.392699) q[32];
u1(0.392699) q[25];
cx q[32], q[25];
u1(-0.392699) q[25];
cx q[32], q[25];
u3(0.785398,0.000000,0.000000) q[25];
cx q[32], q[25];
u3(-0.785398,0.000000,0.000000) q[25];
ccx q[32], q[25], q[24];
ccx q[32], q[24], q[9];
u3(0.785398,0.000000,0.000000) q[24];
cx q[32], q[24];
u3(-0.785398,0.000000,0.000000) q[24];
ccx q[32], q[8], q[24];
u1(-0.392699) q[32];
u1(-0.392699) q[24];
cx q[32], q[24];
u1(0.392699) q[24];
cx q[32], q[24];
ccx q[32], q[23], q[24];
u1(0.392699) q[32];
u1(0.392699) q[24];
cx q[32], q[24];
u1(-0.392699) q[24];
cx q[32], q[24];
ccx q[32], q[8], q[24];
u1(-0.392699) q[32];
u1(-0.392699) q[24];
cx q[32], q[24];
u1(0.392699) q[24];
cx q[32], q[24];
ccx q[32], q[23], q[24];
ccx q[32], q[23], q[8];
u1(-0.392699) q[32];
u1(-0.392699) q[8];
cx q[32], q[8];
u1(0.392699) q[8];
cx q[32], q[8];
ccx q[32], q[23], q[8];
u1(0.392699) q[32];
u1(0.392699) q[23];
cx q[32], q[23];
u1(-0.392699) q[23];
cx q[32], q[23];
u1(0.392699) q[32];
u1(0.392699) q[8];
cx q[32], q[8];
u1(-0.392699) q[8];
cx q[32], q[8];
u1(0.392699) q[32];
u1(0.392699) q[24];
cx q[32], q[24];
u1(-0.392699) q[24];
cx q[32], q[24];
u3(0.785398,0.000000,0.000000) q[24];
cx q[32], q[24];
u3(-0.785398,0.000000,0.000000) q[24];
ccx q[32], q[24], q[23];
ccx q[32], q[23], q[8];
u3(0.785398,0.000000,0.000000) q[23];
cx q[32], q[23];
u3(-0.785398,0.000000,0.000000) q[23];
ccx q[32], q[7], q[23];
u1(-0.392699) q[32];
u1(-0.392699) q[23];
cx q[32], q[23];
u1(0.392699) q[23];
cx q[32], q[23];
ccx q[32], q[22], q[23];
u1(0.392699) q[32];
u1(0.392699) q[23];
cx q[32], q[23];
u1(-0.392699) q[23];
cx q[32], q[23];
ccx q[32], q[7], q[23];
u1(-0.392699) q[32];
u1(-0.392699) q[23];
cx q[32], q[23];
u1(0.392699) q[23];
cx q[32], q[23];
ccx q[32], q[22], q[23];
ccx q[32], q[22], q[7];
u1(-0.392699) q[32];
u1(-0.392699) q[7];
cx q[32], q[7];
u1(0.392699) q[7];
cx q[32], q[7];
ccx q[32], q[22], q[7];
u1(0.392699) q[32];
u1(0.392699) q[22];
cx q[32], q[22];
u1(-0.392699) q[22];
cx q[32], q[22];
u1(0.392699) q[32];
u1(0.392699) q[7];
cx q[32], q[7];
u1(-0.392699) q[7];
cx q[32], q[7];
u1(0.392699) q[32];
u1(0.392699) q[23];
cx q[32], q[23];
u1(-0.392699) q[23];
cx q[32], q[23];
u3(0.785398,0.000000,0.000000) q[23];
cx q[32], q[23];
u3(-0.785398,0.000000,0.000000) q[23];
ccx q[32], q[23], q[22];
ccx q[32], q[22], q[7];
u3(0.785398,0.000000,0.000000) q[22];
cx q[32], q[22];
u3(-0.785398,0.000000,0.000000) q[22];
ccx q[32], q[6], q[22];
u1(-0.392699) q[32];
u1(-0.392699) q[22];
cx q[32], q[22];
u1(0.392699) q[22];
cx q[32], q[22];
ccx q[32], q[21], q[22];
u1(0.392699) q[32];
u1(0.392699) q[22];
cx q[32], q[22];
u1(-0.392699) q[22];
cx q[32], q[22];
ccx q[32], q[6], q[22];
u1(-0.392699) q[32];
u1(-0.392699) q[22];
cx q[32], q[22];
u1(0.392699) q[22];
cx q[32], q[22];
ccx q[32], q[21], q[22];
ccx q[32], q[21], q[6];
u1(-0.392699) q[32];
u1(-0.392699) q[6];
cx q[32], q[6];
u1(0.392699) q[6];
cx q[32], q[6];
ccx q[32], q[21], q[6];
u1(0.392699) q[32];
u1(0.392699) q[21];
cx q[32], q[21];
u1(-0.392699) q[21];
cx q[32], q[21];
u1(0.392699) q[32];
u1(0.392699) q[6];
cx q[32], q[6];
u1(-0.392699) q[6];
cx q[32], q[6];
u1(0.392699) q[32];
u1(0.392699) q[22];
cx q[32], q[22];
u1(-0.392699) q[22];
cx q[32], q[22];
u3(0.785398,0.000000,0.000000) q[22];
cx q[32], q[22];
u3(-0.785398,0.000000,0.000000) q[22];
ccx q[32], q[22], q[21];
ccx q[32], q[21], q[6];
u3(0.785398,0.000000,0.000000) q[21];
cx q[32], q[21];
u3(-0.785398,0.000000,0.000000) q[21];
ccx q[32], q[5], q[21];
u1(-0.392699) q[32];
u1(-0.392699) q[21];
cx q[32], q[21];
u1(0.392699) q[21];
cx q[32], q[21];
ccx q[32], q[20], q[21];
u1(0.392699) q[32];
u1(0.392699) q[21];
cx q[32], q[21];
u1(-0.392699) q[21];
cx q[32], q[21];
ccx q[32], q[5], q[21];
u1(-0.392699) q[32];
u1(-0.392699) q[21];
cx q[32], q[21];
u1(0.392699) q[21];
cx q[32], q[21];
ccx q[32], q[20], q[21];
ccx q[32], q[20], q[5];
u1(-0.392699) q[32];
u1(-0.392699) q[5];
cx q[32], q[5];
u1(0.392699) q[5];
cx q[32], q[5];
ccx q[32], q[20], q[5];
u1(0.392699) q[32];
u1(0.392699) q[20];
cx q[32], q[20];
u1(-0.392699) q[20];
cx q[32], q[20];
u1(0.392699) q[32];
u1(0.392699) q[5];
cx q[32], q[5];
u1(-0.392699) q[5];
cx q[32], q[5];
u1(0.392699) q[32];
u1(0.392699) q[21];
cx q[32], q[21];
u1(-0.392699) q[21];
cx q[32], q[21];
u3(0.785398,0.000000,0.000000) q[21];
cx q[32], q[21];
u3(-0.785398,0.000000,0.000000) q[21];
ccx q[32], q[21], q[20];
ccx q[32], q[20], q[5];
u3(0.785398,0.000000,0.000000) q[20];
cx q[32], q[20];
u3(-0.785398,0.000000,0.000000) q[20];
ccx q[32], q[4], q[20];
u1(-0.392699) q[32];
u1(-0.392699) q[20];
cx q[32], q[20];
u1(0.392699) q[20];
cx q[32], q[20];
ccx q[32], q[19], q[20];
u1(0.392699) q[32];
u1(0.392699) q[20];
cx q[32], q[20];
u1(-0.392699) q[20];
cx q[32], q[20];
ccx q[32], q[4], q[20];
u1(-0.392699) q[32];
u1(-0.392699) q[20];
cx q[32], q[20];
u1(0.392699) q[20];
cx q[32], q[20];
ccx q[32], q[19], q[20];
ccx q[32], q[19], q[4];
u1(-0.392699) q[32];
u1(-0.392699) q[4];
cx q[32], q[4];
u1(0.392699) q[4];
cx q[32], q[4];
ccx q[32], q[19], q[4];
u1(0.392699) q[32];
u1(0.392699) q[19];
cx q[32], q[19];
u1(-0.392699) q[19];
cx q[32], q[19];
u1(0.392699) q[32];
u1(0.392699) q[4];
cx q[32], q[4];
u1(-0.392699) q[4];
cx q[32], q[4];
u1(0.392699) q[32];
u1(0.392699) q[20];
cx q[32], q[20];
u1(-0.392699) q[20];
cx q[32], q[20];
u3(0.785398,0.000000,0.000000) q[20];
cx q[32], q[20];
u3(-0.785398,0.000000,0.000000) q[20];
ccx q[32], q[20], q[19];
ccx q[32], q[19], q[4];
u3(0.785398,0.000000,0.000000) q[19];
cx q[32], q[19];
u3(-0.785398,0.000000,0.000000) q[19];
ccx q[32], q[3], q[19];
u1(-0.392699) q[32];
u1(-0.392699) q[19];
cx q[32], q[19];
u1(0.392699) q[19];
cx q[32], q[19];
ccx q[32], q[18], q[19];
u1(0.392699) q[32];
u1(0.392699) q[19];
cx q[32], q[19];
u1(-0.392699) q[19];
cx q[32], q[19];
ccx q[32], q[3], q[19];
u1(-0.392699) q[32];
u1(-0.392699) q[19];
cx q[32], q[19];
u1(0.392699) q[19];
cx q[32], q[19];
ccx q[32], q[18], q[19];
ccx q[32], q[18], q[3];
u1(-0.392699) q[32];
u1(-0.392699) q[3];
cx q[32], q[3];
u1(0.392699) q[3];
cx q[32], q[3];
ccx q[32], q[18], q[3];
u1(0.392699) q[32];
u1(0.392699) q[18];
cx q[32], q[18];
u1(-0.392699) q[18];
cx q[32], q[18];
u1(0.392699) q[32];
u1(0.392699) q[3];
cx q[32], q[3];
u1(-0.392699) q[3];
cx q[32], q[3];
u1(0.392699) q[32];
u1(0.392699) q[19];
cx q[32], q[19];
u1(-0.392699) q[19];
cx q[32], q[19];
u3(0.785398,0.000000,0.000000) q[19];
cx q[32], q[19];
u3(-0.785398,0.000000,0.000000) q[19];
ccx q[32], q[19], q[18];
ccx q[32], q[18], q[3];
u3(0.785398,0.000000,0.000000) q[18];
cx q[32], q[18];
u3(-0.785398,0.000000,0.000000) q[18];
ccx q[32], q[2], q[18];
u1(-0.392699) q[32];
u1(-0.392699) q[18];
cx q[32], q[18];
u1(0.392699) q[18];
cx q[32], q[18];
ccx q[32], q[17], q[18];
u1(0.392699) q[32];
u1(0.392699) q[18];
cx q[32], q[18];
u1(-0.392699) q[18];
cx q[32], q[18];
ccx q[32], q[2], q[18];
u1(-0.392699) q[32];
u1(-0.392699) q[18];
cx q[32], q[18];
u1(0.392699) q[18];
cx q[32], q[18];
ccx q[32], q[17], q[18];
ccx q[32], q[17], q[2];
u1(-0.392699) q[32];
u1(-0.392699) q[2];
cx q[32], q[2];
u1(0.392699) q[2];
cx q[32], q[2];
ccx q[32], q[17], q[2];
u1(0.392699) q[32];
u1(0.392699) q[17];
cx q[32], q[17];
u1(-0.392699) q[17];
cx q[32], q[17];
u1(0.392699) q[32];
u1(0.392699) q[2];
cx q[32], q[2];
u1(-0.392699) q[2];
cx q[32], q[2];
u1(0.392699) q[32];
u1(0.392699) q[18];
cx q[32], q[18];
u1(-0.392699) q[18];
cx q[32], q[18];
u3(0.785398,0.000000,0.000000) q[18];
cx q[32], q[18];
u3(-0.785398,0.000000,0.000000) q[18];
ccx q[32], q[18], q[17];
ccx q[32], q[17], q[2];
u3(0.785398,0.000000,0.000000) q[17];
cx q[32], q[17];
u3(-0.785398,0.000000,0.000000) q[17];
ccx q[32], q[1], q[17];
u1(-0.392699) q[32];
u1(-0.392699) q[17];
cx q[32], q[17];
u1(0.392699) q[17];
cx q[32], q[17];
ccx q[32], q[16], q[17];
u1(0.392699) q[32];
u1(0.392699) q[17];
cx q[32], q[17];
u1(-0.392699) q[17];
cx q[32], q[17];
ccx q[32], q[1], q[17];
u1(-0.392699) q[32];
u1(-0.392699) q[17];
cx q[32], q[17];
u1(0.392699) q[17];
cx q[32], q[17];
ccx q[32], q[16], q[17];
ccx q[32], q[16], q[1];
u1(-0.392699) q[32];
u1(-0.392699) q[1];
cx q[32], q[1];
u1(0.392699) q[1];
cx q[32], q[1];
ccx q[32], q[16], q[1];
u1(0.392699) q[32];
u1(0.392699) q[16];
cx q[32], q[16];
u1(-0.392699) q[16];
cx q[32], q[16];
u1(0.392699) q[32];
u1(0.392699) q[1];
cx q[32], q[1];
u1(-0.392699) q[1];
cx q[32], q[1];
u1(0.392699) q[32];
u1(0.392699) q[17];
cx q[32], q[17];
u1(-0.392699) q[17];
cx q[32], q[17];
u3(0.785398,0.000000,0.000000) q[17];
cx q[32], q[17];
u3(-0.785398,0.000000,0.000000) q[17];
ccx q[32], q[17], q[16];
ccx q[32], q[16], q[1];
u3(0.785398,0.000000,0.000000) q[16];
cx q[32], q[16];
u3(-0.785398,0.000000,0.000000) q[16];
ccx q[32], q[0], q[16];
u1(-0.392699) q[32];
u1(-0.392699) q[16];
cx q[32], q[16];
u1(0.392699) q[16];
cx q[32], q[16];
ccx q[32], q[48], q[16];
u1(0.392699) q[32];
u1(0.392699) q[16];
cx q[32], q[16];
u1(-0.392699) q[16];
cx q[32], q[16];
ccx q[32], q[0], q[16];
u1(-0.392699) q[32];
u1(-0.392699) q[16];
cx q[32], q[16];
u1(0.392699) q[16];
cx q[32], q[16];
ccx q[32], q[48], q[16];
ccx q[32], q[48], q[0];
u1(-0.392699) q[32];
u1(-0.392699) q[0];
cx q[32], q[0];
u1(0.392699) q[0];
cx q[32], q[0];
ccx q[32], q[48], q[0];
u1(0.392699) q[32];
u1(0.392699) q[48];
cx q[32], q[48];
u1(-0.392699) q[48];
cx q[32], q[48];
u1(0.392699) q[32];
u1(0.392699) q[0];
cx q[32], q[0];
u1(-0.392699) q[0];
cx q[32], q[0];
u1(0.392699) q[32];
u1(0.392699) q[16];
cx q[32], q[16];
u1(-0.392699) q[16];
cx q[32], q[16];
u3(0.785398,0.000000,0.000000) q[16];
cx q[32], q[16];
u3(-0.785398,0.000000,0.000000) q[16];
ccx q[32], q[16], q[48];
ccx q[32], q[48], q[0];
cx q[32], q[31];
cx q[32], q[30];
cx q[32], q[29];
cx q[32], q[28];
cx q[32], q[27];
cx q[32], q[26];
cx q[32], q[25];
cx q[32], q[24];
cx q[32], q[23];
cx q[32], q[22];
cx q[32], q[21];
cx q[32], q[20];
cx q[32], q[19];
cx q[32], q[18];
cx q[32], q[17];
cx q[32], q[16];
cx q[32], q[48];
x q[31];
x q[28];
x q[26];
x q[24];
x q[20];
x q[19];

