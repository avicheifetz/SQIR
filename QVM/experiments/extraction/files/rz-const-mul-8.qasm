OPENQASM 2.0;
include "qelib1.inc";

qreg q[16];

u1(0.000000) q[0];
u1(0.000000) q[8];
u1(0.000000) q[15];
h q[15];
u1(0.000000) q[15];
u1(0.785398) q[14];
u1(0.785398) q[15];
cx q[14], q[15];
u1(-0.785398) q[15];
cx q[14], q[15];
u1(0.392699) q[13];
u1(0.392699) q[15];
cx q[13], q[15];
u1(-0.392699) q[15];
cx q[13], q[15];
u1(0.196350) q[12];
u1(0.196350) q[15];
cx q[12], q[15];
u1(-0.196350) q[15];
cx q[12], q[15];
u1(0.098175) q[11];
u1(0.098175) q[15];
cx q[11], q[15];
u1(-0.098175) q[15];
cx q[11], q[15];
u1(0.049087) q[10];
u1(0.049087) q[15];
cx q[10], q[15];
u1(-0.049087) q[15];
cx q[10], q[15];
u1(0.024544) q[9];
u1(0.024544) q[15];
cx q[9], q[15];
u1(-0.024544) q[15];
cx q[9], q[15];
u1(0.012272) q[8];
u1(0.012272) q[15];
cx q[8], q[15];
u1(-0.012272) q[15];
cx q[8], q[15];
h q[14];
u1(0.000000) q[14];
u1(0.785398) q[13];
u1(0.785398) q[14];
cx q[13], q[14];
u1(-0.785398) q[14];
cx q[13], q[14];
u1(0.392699) q[12];
u1(0.392699) q[14];
cx q[12], q[14];
u1(-0.392699) q[14];
cx q[12], q[14];
u1(0.196350) q[11];
u1(0.196350) q[14];
cx q[11], q[14];
u1(-0.196350) q[14];
cx q[11], q[14];
u1(0.098175) q[10];
u1(0.098175) q[14];
cx q[10], q[14];
u1(-0.098175) q[14];
cx q[10], q[14];
u1(0.049087) q[9];
u1(0.049087) q[14];
cx q[9], q[14];
u1(-0.049087) q[14];
cx q[9], q[14];
u1(0.024544) q[8];
u1(0.024544) q[14];
cx q[8], q[14];
u1(-0.024544) q[14];
cx q[8], q[14];
h q[13];
u1(0.000000) q[13];
u1(0.785398) q[12];
u1(0.785398) q[13];
cx q[12], q[13];
u1(-0.785398) q[13];
cx q[12], q[13];
u1(0.392699) q[11];
u1(0.392699) q[13];
cx q[11], q[13];
u1(-0.392699) q[13];
cx q[11], q[13];
u1(0.196350) q[10];
u1(0.196350) q[13];
cx q[10], q[13];
u1(-0.196350) q[13];
cx q[10], q[13];
u1(0.098175) q[9];
u1(0.098175) q[13];
cx q[9], q[13];
u1(-0.098175) q[13];
cx q[9], q[13];
u1(0.049087) q[8];
u1(0.049087) q[13];
cx q[8], q[13];
u1(-0.049087) q[13];
cx q[8], q[13];
h q[12];
u1(0.000000) q[12];
u1(0.785398) q[11];
u1(0.785398) q[12];
cx q[11], q[12];
u1(-0.785398) q[12];
cx q[11], q[12];
u1(0.392699) q[10];
u1(0.392699) q[12];
cx q[10], q[12];
u1(-0.392699) q[12];
cx q[10], q[12];
u1(0.196350) q[9];
u1(0.196350) q[12];
cx q[9], q[12];
u1(-0.196350) q[12];
cx q[9], q[12];
u1(0.098175) q[8];
u1(0.098175) q[12];
cx q[8], q[12];
u1(-0.098175) q[12];
cx q[8], q[12];
h q[11];
u1(0.000000) q[11];
u1(0.785398) q[10];
u1(0.785398) q[11];
cx q[10], q[11];
u1(-0.785398) q[11];
cx q[10], q[11];
u1(0.392699) q[9];
u1(0.392699) q[11];
cx q[9], q[11];
u1(-0.392699) q[11];
cx q[9], q[11];
u1(0.196350) q[8];
u1(0.196350) q[11];
cx q[8], q[11];
u1(-0.196350) q[11];
cx q[8], q[11];
h q[10];
u1(0.000000) q[10];
u1(0.785398) q[9];
u1(0.785398) q[10];
cx q[9], q[10];
u1(-0.785398) q[10];
cx q[9], q[10];
u1(0.392699) q[8];
u1(0.392699) q[10];
cx q[8], q[10];
u1(-0.392699) q[10];
cx q[8], q[10];
h q[9];
u1(0.000000) q[9];
u1(0.785398) q[8];
u1(0.785398) q[9];
cx q[8], q[9];
u1(-0.785398) q[9];
cx q[8], q[9];
h q[8];
u1(0.000000) q[8];
u1(0.000000) q[7];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.000000) q[7];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.012272) q[7];
u1(0.012272) q[15];
cx q[7], q[15];
u1(-0.012272) q[15];
cx q[7], q[15];
u1(0.024544) q[7];
u1(0.024544) q[14];
cx q[7], q[14];
u1(-0.024544) q[14];
cx q[7], q[14];
u1(0.049087) q[7];
u1(0.049087) q[13];
cx q[7], q[13];
u1(-0.049087) q[13];
cx q[7], q[13];
u1(0.098175) q[7];
u1(0.098175) q[12];
cx q[7], q[12];
u1(-0.098175) q[12];
cx q[7], q[12];
u1(0.196350) q[7];
u1(0.196350) q[11];
cx q[7], q[11];
u1(-0.196350) q[11];
cx q[7], q[11];
u1(0.392699) q[7];
u1(0.392699) q[10];
cx q[7], q[10];
u1(-0.392699) q[10];
cx q[7], q[10];
u1(0.785398) q[7];
u1(0.785398) q[9];
cx q[7], q[9];
u1(-0.785398) q[9];
cx q[7], q[9];
u1(1.570796) q[7];
u1(1.570796) q[8];
cx q[7], q[8];
u1(-1.570796) q[8];
cx q[7], q[8];
u1(0.000000) q[7];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.024544) q[7];
u1(0.024544) q[15];
cx q[7], q[15];
u1(-0.024544) q[15];
cx q[7], q[15];
u1(0.049087) q[7];
u1(0.049087) q[14];
cx q[7], q[14];
u1(-0.049087) q[14];
cx q[7], q[14];
u1(0.098175) q[7];
u1(0.098175) q[13];
cx q[7], q[13];
u1(-0.098175) q[13];
cx q[7], q[13];
u1(0.196350) q[7];
u1(0.196350) q[12];
cx q[7], q[12];
u1(-0.196350) q[12];
cx q[7], q[12];
u1(0.392699) q[7];
u1(0.392699) q[11];
cx q[7], q[11];
u1(-0.392699) q[11];
cx q[7], q[11];
u1(0.785398) q[7];
u1(0.785398) q[10];
cx q[7], q[10];
u1(-0.785398) q[10];
cx q[7], q[10];
u1(1.570796) q[7];
u1(1.570796) q[9];
cx q[7], q[9];
u1(-1.570796) q[9];
cx q[7], q[9];
u1(0.000000) q[7];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.049087) q[7];
u1(0.049087) q[15];
cx q[7], q[15];
u1(-0.049087) q[15];
cx q[7], q[15];
u1(0.098175) q[7];
u1(0.098175) q[14];
cx q[7], q[14];
u1(-0.098175) q[14];
cx q[7], q[14];
u1(0.196350) q[7];
u1(0.196350) q[13];
cx q[7], q[13];
u1(-0.196350) q[13];
cx q[7], q[13];
u1(0.392699) q[7];
u1(0.392699) q[12];
cx q[7], q[12];
u1(-0.392699) q[12];
cx q[7], q[12];
u1(0.785398) q[7];
u1(0.785398) q[11];
cx q[7], q[11];
u1(-0.785398) q[11];
cx q[7], q[11];
u1(1.570796) q[7];
u1(1.570796) q[10];
cx q[7], q[10];
u1(-1.570796) q[10];
cx q[7], q[10];
u1(0.000000) q[7];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.098175) q[7];
u1(0.098175) q[15];
cx q[7], q[15];
u1(-0.098175) q[15];
cx q[7], q[15];
u1(0.196350) q[7];
u1(0.196350) q[14];
cx q[7], q[14];
u1(-0.196350) q[14];
cx q[7], q[14];
u1(0.392699) q[7];
u1(0.392699) q[13];
cx q[7], q[13];
u1(-0.392699) q[13];
cx q[7], q[13];
u1(0.785398) q[7];
u1(0.785398) q[12];
cx q[7], q[12];
u1(-0.785398) q[12];
cx q[7], q[12];
u1(1.570796) q[7];
u1(1.570796) q[11];
cx q[7], q[11];
u1(-1.570796) q[11];
cx q[7], q[11];
u1(0.000000) q[7];
u1(0.000000) q[11];
cx q[7], q[11];
u1(0.000000) q[11];
cx q[7], q[11];
u1(0.000000) q[7];
u1(0.000000) q[10];
cx q[7], q[10];
u1(0.000000) q[10];
cx q[7], q[10];
u1(0.000000) q[7];
u1(0.000000) q[9];
cx q[7], q[9];
u1(0.000000) q[9];
cx q[7], q[9];
u1(0.000000) q[7];
u1(0.000000) q[15];
cx q[7], q[15];
u1(0.000000) q[15];
cx q[7], q[15];
u1(1.570796) q[7];
u1(1.570796) q[15];
cx q[7], q[15];
u1(-1.570796) q[15];
cx q[7], q[15];
u1(0.000000) q[6];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.000000) q[6];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.000000) q[6];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.024544) q[6];
u1(0.024544) q[15];
cx q[6], q[15];
u1(-0.024544) q[15];
cx q[6], q[15];
u1(0.049087) q[6];
u1(0.049087) q[14];
cx q[6], q[14];
u1(-0.049087) q[14];
cx q[6], q[14];
u1(0.098175) q[6];
u1(0.098175) q[13];
cx q[6], q[13];
u1(-0.098175) q[13];
cx q[6], q[13];
u1(0.196350) q[6];
u1(0.196350) q[12];
cx q[6], q[12];
u1(-0.196350) q[12];
cx q[6], q[12];
u1(0.392699) q[6];
u1(0.392699) q[11];
cx q[6], q[11];
u1(-0.392699) q[11];
cx q[6], q[11];
u1(0.785398) q[6];
u1(0.785398) q[10];
cx q[6], q[10];
u1(-0.785398) q[10];
cx q[6], q[10];
u1(1.570796) q[6];
u1(1.570796) q[9];
cx q[6], q[9];
u1(-1.570796) q[9];
cx q[6], q[9];
u1(0.000000) q[6];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.049087) q[6];
u1(0.049087) q[15];
cx q[6], q[15];
u1(-0.049087) q[15];
cx q[6], q[15];
u1(0.098175) q[6];
u1(0.098175) q[14];
cx q[6], q[14];
u1(-0.098175) q[14];
cx q[6], q[14];
u1(0.196350) q[6];
u1(0.196350) q[13];
cx q[6], q[13];
u1(-0.196350) q[13];
cx q[6], q[13];
u1(0.392699) q[6];
u1(0.392699) q[12];
cx q[6], q[12];
u1(-0.392699) q[12];
cx q[6], q[12];
u1(0.785398) q[6];
u1(0.785398) q[11];
cx q[6], q[11];
u1(-0.785398) q[11];
cx q[6], q[11];
u1(1.570796) q[6];
u1(1.570796) q[10];
cx q[6], q[10];
u1(-1.570796) q[10];
cx q[6], q[10];
u1(0.000000) q[6];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.098175) q[6];
u1(0.098175) q[15];
cx q[6], q[15];
u1(-0.098175) q[15];
cx q[6], q[15];
u1(0.196350) q[6];
u1(0.196350) q[14];
cx q[6], q[14];
u1(-0.196350) q[14];
cx q[6], q[14];
u1(0.392699) q[6];
u1(0.392699) q[13];
cx q[6], q[13];
u1(-0.392699) q[13];
cx q[6], q[13];
u1(0.785398) q[6];
u1(0.785398) q[12];
cx q[6], q[12];
u1(-0.785398) q[12];
cx q[6], q[12];
u1(1.570796) q[6];
u1(1.570796) q[11];
cx q[6], q[11];
u1(-1.570796) q[11];
cx q[6], q[11];
u1(0.000000) q[6];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.000000) q[15];
cx q[6], q[15];
u1(0.196350) q[6];
u1(0.196350) q[15];
cx q[6], q[15];
u1(-0.196350) q[15];
cx q[6], q[15];
u1(0.392699) q[6];
u1(0.392699) q[14];
cx q[6], q[14];
u1(-0.392699) q[14];
cx q[6], q[14];
u1(0.785398) q[6];
u1(0.785398) q[13];
cx q[6], q[13];
u1(-0.785398) q[13];
cx q[6], q[13];
u1(1.570796) q[6];
u1(1.570796) q[12];
cx q[6], q[12];
u1(-1.570796) q[12];
cx q[6], q[12];
u1(0.000000) q[6];
u1(0.000000) q[10];
cx q[6], q[10];
u1(0.000000) q[10];
cx q[6], q[10];
u1(0.000000) q[6];
u1(0.000000) q[9];
cx q[6], q[9];
u1(0.000000) q[9];
cx q[6], q[9];
u1(0.000000) q[6];
u1(0.000000) q[8];
cx q[6], q[8];
u1(0.000000) q[8];
cx q[6], q[8];
u1(0.000000) q[5];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.000000) q[5];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.000000) q[5];
u1(0.000000) q[14];
cx q[5], q[14];
u1(0.000000) q[14];
cx q[5], q[14];
u1(0.000000) q[5];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.049087) q[5];
u1(0.049087) q[15];
cx q[5], q[15];
u1(-0.049087) q[15];
cx q[5], q[15];
u1(0.098175) q[5];
u1(0.098175) q[14];
cx q[5], q[14];
u1(-0.098175) q[14];
cx q[5], q[14];
u1(0.196350) q[5];
u1(0.196350) q[13];
cx q[5], q[13];
u1(-0.196350) q[13];
cx q[5], q[13];
u1(0.392699) q[5];
u1(0.392699) q[12];
cx q[5], q[12];
u1(-0.392699) q[12];
cx q[5], q[12];
u1(0.785398) q[5];
u1(0.785398) q[11];
cx q[5], q[11];
u1(-0.785398) q[11];
cx q[5], q[11];
u1(1.570796) q[5];
u1(1.570796) q[10];
cx q[5], q[10];
u1(-1.570796) q[10];
cx q[5], q[10];
u1(0.000000) q[5];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.098175) q[5];
u1(0.098175) q[15];
cx q[5], q[15];
u1(-0.098175) q[15];
cx q[5], q[15];
u1(0.196350) q[5];
u1(0.196350) q[14];
cx q[5], q[14];
u1(-0.196350) q[14];
cx q[5], q[14];
u1(0.392699) q[5];
u1(0.392699) q[13];
cx q[5], q[13];
u1(-0.392699) q[13];
cx q[5], q[13];
u1(0.785398) q[5];
u1(0.785398) q[12];
cx q[5], q[12];
u1(-0.785398) q[12];
cx q[5], q[12];
u1(1.570796) q[5];
u1(1.570796) q[11];
cx q[5], q[11];
u1(-1.570796) q[11];
cx q[5], q[11];
u1(0.000000) q[5];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.196350) q[5];
u1(0.196350) q[15];
cx q[5], q[15];
u1(-0.196350) q[15];
cx q[5], q[15];
u1(0.392699) q[5];
u1(0.392699) q[14];
cx q[5], q[14];
u1(-0.392699) q[14];
cx q[5], q[14];
u1(0.785398) q[5];
u1(0.785398) q[13];
cx q[5], q[13];
u1(-0.785398) q[13];
cx q[5], q[13];
u1(1.570796) q[5];
u1(1.570796) q[12];
cx q[5], q[12];
u1(-1.570796) q[12];
cx q[5], q[12];
u1(0.000000) q[5];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.000000) q[15];
cx q[5], q[15];
u1(0.392699) q[5];
u1(0.392699) q[15];
cx q[5], q[15];
u1(-0.392699) q[15];
cx q[5], q[15];
u1(0.785398) q[5];
u1(0.785398) q[14];
cx q[5], q[14];
u1(-0.785398) q[14];
cx q[5], q[14];
u1(1.570796) q[5];
u1(1.570796) q[13];
cx q[5], q[13];
u1(-1.570796) q[13];
cx q[5], q[13];
u1(0.000000) q[5];
u1(0.000000) q[9];
cx q[5], q[9];
u1(0.000000) q[9];
cx q[5], q[9];
u1(0.000000) q[5];
u1(0.000000) q[8];
cx q[5], q[8];
u1(0.000000) q[8];
cx q[5], q[8];
u1(0.000000) q[4];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.000000) q[4];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.000000) q[4];
u1(0.000000) q[14];
cx q[4], q[14];
u1(0.000000) q[14];
cx q[4], q[14];
u1(0.000000) q[4];
u1(0.000000) q[13];
cx q[4], q[13];
u1(0.000000) q[13];
cx q[4], q[13];
u1(0.000000) q[4];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.098175) q[4];
u1(0.098175) q[15];
cx q[4], q[15];
u1(-0.098175) q[15];
cx q[4], q[15];
u1(0.196350) q[4];
u1(0.196350) q[14];
cx q[4], q[14];
u1(-0.196350) q[14];
cx q[4], q[14];
u1(0.392699) q[4];
u1(0.392699) q[13];
cx q[4], q[13];
u1(-0.392699) q[13];
cx q[4], q[13];
u1(0.785398) q[4];
u1(0.785398) q[12];
cx q[4], q[12];
u1(-0.785398) q[12];
cx q[4], q[12];
u1(1.570796) q[4];
u1(1.570796) q[11];
cx q[4], q[11];
u1(-1.570796) q[11];
cx q[4], q[11];
u1(0.000000) q[4];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.196350) q[4];
u1(0.196350) q[15];
cx q[4], q[15];
u1(-0.196350) q[15];
cx q[4], q[15];
u1(0.392699) q[4];
u1(0.392699) q[14];
cx q[4], q[14];
u1(-0.392699) q[14];
cx q[4], q[14];
u1(0.785398) q[4];
u1(0.785398) q[13];
cx q[4], q[13];
u1(-0.785398) q[13];
cx q[4], q[13];
u1(1.570796) q[4];
u1(1.570796) q[12];
cx q[4], q[12];
u1(-1.570796) q[12];
cx q[4], q[12];
u1(0.000000) q[4];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.392699) q[4];
u1(0.392699) q[15];
cx q[4], q[15];
u1(-0.392699) q[15];
cx q[4], q[15];
u1(0.785398) q[4];
u1(0.785398) q[14];
cx q[4], q[14];
u1(-0.785398) q[14];
cx q[4], q[14];
u1(1.570796) q[4];
u1(1.570796) q[13];
cx q[4], q[13];
u1(-1.570796) q[13];
cx q[4], q[13];
u1(0.000000) q[4];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.000000) q[15];
cx q[4], q[15];
u1(0.785398) q[4];
u1(0.785398) q[15];
cx q[4], q[15];
u1(-0.785398) q[15];
cx q[4], q[15];
u1(1.570796) q[4];
u1(1.570796) q[14];
cx q[4], q[14];
u1(-1.570796) q[14];
cx q[4], q[14];
u1(0.000000) q[4];
u1(0.000000) q[8];
cx q[4], q[8];
u1(0.000000) q[8];
cx q[4], q[8];
u1(0.000000) q[3];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.000000) q[3];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.000000) q[3];
u1(0.000000) q[14];
cx q[3], q[14];
u1(0.000000) q[14];
cx q[3], q[14];
u1(0.000000) q[3];
u1(0.000000) q[13];
cx q[3], q[13];
u1(0.000000) q[13];
cx q[3], q[13];
u1(0.000000) q[3];
u1(0.000000) q[12];
cx q[3], q[12];
u1(0.000000) q[12];
cx q[3], q[12];
u1(0.000000) q[3];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.196350) q[3];
u1(0.196350) q[15];
cx q[3], q[15];
u1(-0.196350) q[15];
cx q[3], q[15];
u1(0.392699) q[3];
u1(0.392699) q[14];
cx q[3], q[14];
u1(-0.392699) q[14];
cx q[3], q[14];
u1(0.785398) q[3];
u1(0.785398) q[13];
cx q[3], q[13];
u1(-0.785398) q[13];
cx q[3], q[13];
u1(1.570796) q[3];
u1(1.570796) q[12];
cx q[3], q[12];
u1(-1.570796) q[12];
cx q[3], q[12];
u1(0.000000) q[3];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.392699) q[3];
u1(0.392699) q[15];
cx q[3], q[15];
u1(-0.392699) q[15];
cx q[3], q[15];
u1(0.785398) q[3];
u1(0.785398) q[14];
cx q[3], q[14];
u1(-0.785398) q[14];
cx q[3], q[14];
u1(1.570796) q[3];
u1(1.570796) q[13];
cx q[3], q[13];
u1(-1.570796) q[13];
cx q[3], q[13];
u1(0.000000) q[3];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.785398) q[3];
u1(0.785398) q[15];
cx q[3], q[15];
u1(-0.785398) q[15];
cx q[3], q[15];
u1(1.570796) q[3];
u1(1.570796) q[14];
cx q[3], q[14];
u1(-1.570796) q[14];
cx q[3], q[14];
u1(0.000000) q[3];
u1(0.000000) q[15];
cx q[3], q[15];
u1(0.000000) q[15];
cx q[3], q[15];
u1(1.570796) q[3];
u1(1.570796) q[15];
cx q[3], q[15];
u1(-1.570796) q[15];
cx q[3], q[15];
u1(0.000000) q[2];
u1(0.000000) q[15];
cx q[2], q[15];
u1(0.000000) q[15];
cx q[2], q[15];
u1(0.000000) q[2];
u1(0.000000) q[15];
cx q[2], q[15];
u1(0.000000) q[15];
cx q[2], q[15];
u1(0.000000) q[2];
u1(0.000000) q[14];
cx q[2], q[14];
u1(0.000000) q[14];
cx q[2], q[14];
u1(0.000000) q[2];
u1(0.000000) q[13];
cx q[2], q[13];
u1(0.000000) q[13];
cx q[2], q[13];
u1(0.000000) q[2];
u1(0.000000) q[12];
cx q[2], q[12];
u1(0.000000) q[12];
cx q[2], q[12];
u1(0.000000) q[2];
u1(0.000000) q[11];
cx q[2], q[11];
u1(0.000000) q[11];
cx q[2], q[11];
u1(0.000000) q[2];
u1(0.000000) q[15];
cx q[2], q[15];
u1(0.000000) q[15];
cx q[2], q[15];
u1(0.392699) q[2];
u1(0.392699) q[15];
cx q[2], q[15];
u1(-0.392699) q[15];
cx q[2], q[15];
u1(0.785398) q[2];
u1(0.785398) q[14];
cx q[2], q[14];
u1(-0.785398) q[14];
cx q[2], q[14];
u1(1.570796) q[2];
u1(1.570796) q[13];
cx q[2], q[13];
u1(-1.570796) q[13];
cx q[2], q[13];
u1(0.000000) q[2];
u1(0.000000) q[15];
cx q[2], q[15];
u1(0.000000) q[15];
cx q[2], q[15];
u1(0.785398) q[2];
u1(0.785398) q[15];
cx q[2], q[15];
u1(-0.785398) q[15];
cx q[2], q[15];
u1(1.570796) q[2];
u1(1.570796) q[14];
cx q[2], q[14];
u1(-1.570796) q[14];
cx q[2], q[14];
u1(0.000000) q[2];
u1(0.000000) q[15];
cx q[2], q[15];
u1(0.000000) q[15];
cx q[2], q[15];
u1(1.570796) q[2];
u1(1.570796) q[15];
cx q[2], q[15];
u1(-1.570796) q[15];
cx q[2], q[15];
u1(0.000000) q[1];
u1(0.000000) q[15];
cx q[1], q[15];
u1(0.000000) q[15];
cx q[1], q[15];
u1(0.000000) q[1];
u1(0.000000) q[15];
cx q[1], q[15];
u1(0.000000) q[15];
cx q[1], q[15];
u1(0.000000) q[1];
u1(0.000000) q[14];
cx q[1], q[14];
u1(0.000000) q[14];
cx q[1], q[14];
u1(0.000000) q[1];
u1(0.000000) q[13];
cx q[1], q[13];
u1(0.000000) q[13];
cx q[1], q[13];
u1(0.000000) q[1];
u1(0.000000) q[12];
cx q[1], q[12];
u1(0.000000) q[12];
cx q[1], q[12];
u1(0.000000) q[1];
u1(0.000000) q[11];
cx q[1], q[11];
u1(0.000000) q[11];
cx q[1], q[11];
u1(0.000000) q[1];
u1(0.000000) q[10];
cx q[1], q[10];
u1(0.000000) q[10];
cx q[1], q[10];
u1(0.000000) q[1];
u1(0.000000) q[15];
cx q[1], q[15];
u1(0.000000) q[15];
cx q[1], q[15];
u1(0.785398) q[1];
u1(0.785398) q[15];
cx q[1], q[15];
u1(-0.785398) q[15];
cx q[1], q[15];
u1(1.570796) q[1];
u1(1.570796) q[14];
cx q[1], q[14];
u1(-1.570796) q[14];
cx q[1], q[14];
u1(0.000000) q[1];
u1(0.000000) q[15];
cx q[1], q[15];
u1(0.000000) q[15];
cx q[1], q[15];
u1(1.570796) q[1];
u1(1.570796) q[15];
cx q[1], q[15];
u1(-1.570796) q[15];
cx q[1], q[15];
u1(0.000000) q[0];
u1(0.000000) q[15];
cx q[0], q[15];
u1(0.000000) q[15];
cx q[0], q[15];
u1(0.000000) q[0];
u1(0.000000) q[15];
cx q[0], q[15];
u1(0.000000) q[15];
cx q[0], q[15];
u1(0.000000) q[0];
u1(0.000000) q[14];
cx q[0], q[14];
u1(0.000000) q[14];
cx q[0], q[14];
u1(0.000000) q[0];
u1(0.000000) q[13];
cx q[0], q[13];
u1(0.000000) q[13];
cx q[0], q[13];
u1(0.000000) q[0];
u1(0.000000) q[12];
cx q[0], q[12];
u1(0.000000) q[12];
cx q[0], q[12];
u1(0.000000) q[0];
u1(0.000000) q[11];
cx q[0], q[11];
u1(0.000000) q[11];
cx q[0], q[11];
u1(0.000000) q[0];
u1(0.000000) q[10];
cx q[0], q[10];
u1(0.000000) q[10];
cx q[0], q[10];
u1(0.000000) q[0];
u1(0.000000) q[9];
cx q[0], q[9];
u1(0.000000) q[9];
cx q[0], q[9];
u1(0.000000) q[0];
u1(0.000000) q[15];
cx q[0], q[15];
u1(0.000000) q[15];
cx q[0], q[15];
u1(1.570796) q[0];
u1(1.570796) q[15];
cx q[0], q[15];
u1(-1.570796) q[15];
cx q[0], q[15];
u1(0.000000) q[7];
u1(0.000000) q[8];
h q[8];
cx q[8], q[9];
u1(0.785398) q[9];
cx q[8], q[9];
u1(-0.785398) q[9];
u1(-0.785398) q[8];
u1(0.000000) q[9];
h q[9];
cx q[8], q[10];
u1(0.392699) q[10];
cx q[8], q[10];
u1(-0.392699) q[10];
u1(-0.392699) q[8];
cx q[9], q[10];
u1(0.785398) q[10];
cx q[9], q[10];
u1(-0.785398) q[10];
u1(-0.785398) q[9];
u1(0.000000) q[10];
h q[10];
cx q[8], q[11];
u1(0.196350) q[11];
cx q[8], q[11];
u1(-0.196350) q[11];
u1(-0.196350) q[8];
cx q[9], q[11];
u1(0.392699) q[11];
cx q[9], q[11];
u1(-0.392699) q[11];
u1(-0.392699) q[9];
cx q[10], q[11];
u1(0.785398) q[11];
cx q[10], q[11];
u1(-0.785398) q[11];
u1(-0.785398) q[10];
u1(0.000000) q[11];
h q[11];
cx q[8], q[12];
u1(0.098175) q[12];
cx q[8], q[12];
u1(-0.098175) q[12];
u1(-0.098175) q[8];
cx q[9], q[12];
u1(0.196350) q[12];
cx q[9], q[12];
u1(-0.196350) q[12];
u1(-0.196350) q[9];
cx q[10], q[12];
u1(0.392699) q[12];
cx q[10], q[12];
u1(-0.392699) q[12];
u1(-0.392699) q[10];
cx q[11], q[12];
u1(0.785398) q[12];
cx q[11], q[12];
u1(-0.785398) q[12];
u1(-0.785398) q[11];
u1(0.000000) q[12];
h q[12];
cx q[8], q[13];
u1(0.049087) q[13];
cx q[8], q[13];
u1(-0.049087) q[13];
u1(-0.049087) q[8];
cx q[9], q[13];
u1(0.098175) q[13];
cx q[9], q[13];
u1(-0.098175) q[13];
u1(-0.098175) q[9];
cx q[10], q[13];
u1(0.196350) q[13];
cx q[10], q[13];
u1(-0.196350) q[13];
u1(-0.196350) q[10];
cx q[11], q[13];
u1(0.392699) q[13];
cx q[11], q[13];
u1(-0.392699) q[13];
u1(-0.392699) q[11];
cx q[12], q[13];
u1(0.785398) q[13];
cx q[12], q[13];
u1(-0.785398) q[13];
u1(-0.785398) q[12];
u1(0.000000) q[13];
h q[13];
cx q[8], q[14];
u1(0.024544) q[14];
cx q[8], q[14];
u1(-0.024544) q[14];
u1(-0.024544) q[8];
cx q[9], q[14];
u1(0.049087) q[14];
cx q[9], q[14];
u1(-0.049087) q[14];
u1(-0.049087) q[9];
cx q[10], q[14];
u1(0.098175) q[14];
cx q[10], q[14];
u1(-0.098175) q[14];
u1(-0.098175) q[10];
cx q[11], q[14];
u1(0.196350) q[14];
cx q[11], q[14];
u1(-0.196350) q[14];
u1(-0.196350) q[11];
cx q[12], q[14];
u1(0.392699) q[14];
cx q[12], q[14];
u1(-0.392699) q[14];
u1(-0.392699) q[12];
cx q[13], q[14];
u1(0.785398) q[14];
cx q[13], q[14];
u1(-0.785398) q[14];
u1(-0.785398) q[13];
u1(0.000000) q[14];
h q[14];
cx q[8], q[15];
u1(0.012272) q[15];
cx q[8], q[15];
u1(-0.012272) q[15];
u1(-0.012272) q[8];
cx q[9], q[15];
u1(0.024544) q[15];
cx q[9], q[15];
u1(-0.024544) q[15];
u1(-0.024544) q[9];
cx q[10], q[15];
u1(0.049087) q[15];
cx q[10], q[15];
u1(-0.049087) q[15];
u1(-0.049087) q[10];
cx q[11], q[15];
u1(0.098175) q[15];
cx q[11], q[15];
u1(-0.098175) q[15];
u1(-0.098175) q[11];
cx q[12], q[15];
u1(0.196350) q[15];
cx q[12], q[15];
u1(-0.196350) q[15];
u1(-0.196350) q[12];
cx q[13], q[15];
u1(0.392699) q[15];
cx q[13], q[15];
u1(-0.392699) q[15];
u1(-0.392699) q[13];
cx q[14], q[15];
u1(0.785398) q[15];
cx q[14], q[15];
u1(-0.785398) q[15];
u1(-0.785398) q[14];
u1(0.000000) q[15];
h q[15];
u1(0.000000) q[15];
u1(0.000000) q[15];
u1(0.000000) q[7];

