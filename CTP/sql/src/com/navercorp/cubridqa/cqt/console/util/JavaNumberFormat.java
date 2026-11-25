/**
 * Copyright (c) 2016, Search Solution Corporation. All rights reserved.
 *
 * <p>Redistribution and use in source and binary forms, with or without modification, are permitted
 * provided that the following conditions are met:
 *
 * <p>* Redistributions of source code must retain the above copyright notice, this list of
 * conditions and the following disclaimer.
 *
 * <p>* Redistributions in binary form must reproduce the above copyright notice, this list of
 * conditions and the following disclaimer in the documentation and/or other materials provided with
 * the distribution.
 *
 * <p>* Neither the name of the copyright holder nor the names of its contributors may be used to
 * endorse or promote products derived from this software without specific prior written permission.
 *
 * <p>THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
 * FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
 * WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package com.navercorp.cubridqa.cqt.console.util;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * APIS-1143: the text of a float or a double as Float.toString/Double.toString give it since JDK
 * 19 (JDK-4511638), whatever JDK runs cqt. JDK 8 to 18 sometimes print more digits than needed
 * (2.14748365E9 for 2^31, where 2.1474836E9 reads back as the same float). Written from the
 * specification in the Double.toString javadoc of JDK 19, not from the JDK source:
 *
 * <ul>
 *   <li>R is the set of decimals that round to v (round half to even); m is the least length of
 *       a decimal in R.
 *   <li>T is the set of decimals in R of length m, or of length 1 or 2 when m is 1.
 *   <li>The decimal in T closest to v is chosen; of two, the one with the even last digit.
 *   <li>It is written plain when 1e-3 <= |v| < 1e7 ("111.26", "1234567.0"), else as d.dddEn.
 * </ul>
 *
 * sql_by_cci prints the same text with java_number_str() in CTP/sql_by_cci/execute.c.
 */
public class JavaNumberFormat {

    public static String toString(float v) {
        if (Float.isNaN(v) || Float.isInfinite(v) || v == 0) {
            return Float.toString(v);
        }
        return format(v, true);
    }

    public static String toString(double v) {
        if (Double.isNaN(v) || Double.isInfinite(v) || v == 0) {
            return Double.toString(v);
        }
        return format(v, false);
    }

    private static String format(double v, boolean isFloat) {
        /* the exact value of v, as a digit string and the exponent of its first digit */
        BigDecimal exact = new BigDecimal(Math.abs(v));
        String all = exact.unscaledValue().toString();
        int exp10 = all.length() - 1 - exact.scale();

        String[] best = null;
        for (int n = 1; n <= 17; n++) {
            best = pick(all, exp10, n, v, isFloat);
            if (best != null) {
                if (n == 1) {
                    /* m == 1: the closest of length 1 or 2, which is the closest of length 2 */
                    best = pick(all, exp10, 2, v, isFloat);
                }
                break;
            }
        }
        String digits = stripZeros(best[0]);
        return layout(v < 0, digits, Integer.parseInt(best[1]));
    }

    /**
     * The decimal of n digits in R closest to v, as {digits, exponent of the first digit}, or null
     * when no decimal of n digits rounds to v. Only the two decimals of n digits around v can.
     */
    private static String[] pick(String all, int exp10, int n, double v, boolean isFloat) {
        String trunc = padRight(all, n).substring(0, n);
        String rest = all.length() > n ? all.substring(n) : "";
        boolean exact = rest.replace("0", "").isEmpty();

        String[] down = {trunc, Integer.toString(exp10)};
        String[] up = exact ? null : increment(trunc, exp10);

        boolean downOk = roundsTo(down, v, isFloat);
        boolean upOk = up != null && roundsTo(up, v, isFloat);
        if (downOk && upOk) {
            int c = compareHalf(rest);
            if (c < 0) {
                return down;
            }
            if (c > 0) {
                return up;
            }
            return (trunc.charAt(n - 1) - '0') % 2 == 0 ? down : up;
        }
        if (downOk) {
            return down;
        }
        if (upOk) {
            return up;
        }
        return null;
    }

    /* 1 when rest (the digits after the first n) is above one half of the last digit, -1 below, 0 at it */
    private static int compareHalf(String rest) {
        if (rest.charAt(0) != '5') {
            return rest.charAt(0) > '5' ? 1 : -1;
        }
        return rest.substring(1).replace("0", "").isEmpty() ? 0 : 1;
    }

    private static String[] increment(String trunc, int exp10) {
        String s = new BigInteger(trunc).add(BigInteger.ONE).toString();
        if (s.length() > trunc.length()) {
            /* 99..9 + 1: 10^n, which is 1 followed by zeros one place up */
            return new String[] {s.substring(0, trunc.length()), Integer.toString(exp10 + 1)};
        }
        return new String[] {s, Integer.toString(exp10)};
    }

    private static boolean roundsTo(String[] d, double v, boolean isFloat) {
        String text = d[0].charAt(0) + "." + (d[0].length() > 1 ? d[0].substring(1) : "0") + "E" + d[1];
        if (isFloat) {
            return Float.parseFloat(text) == (float) Math.abs(v);
        }
        return Double.parseDouble(text) == Math.abs(v);
    }

    private static String stripZeros(String digits) {
        int k = digits.length();
        while (k > 1 && digits.charAt(k - 1) == '0') {
            k--;
        }
        return digits.substring(0, k);
    }

    private static String padRight(String s, int n) {
        StringBuilder sb = new StringBuilder(s);
        while (sb.length() < n) {
            sb.append('0');
        }
        return sb.toString();
    }

    /* the layout of Float.toString/Double.toString, the same in every JDK */
    private static String layout(boolean negative, String digits, int exp10) {
        StringBuilder sb = new StringBuilder();
        if (negative) {
            sb.append('-');
        }
        int nd = digits.length();
        if (exp10 >= -3 && exp10 < 7) {
            if (exp10 >= 0) {
                sb.append(padRight(digits, exp10 + 1), 0, exp10 + 1);
                sb.append('.');
                sb.append(nd > exp10 + 1 ? digits.substring(exp10 + 1) : "0");
            } else {
                sb.append("0.");
                for (int k = 0; k < -exp10 - 1; k++) {
                    sb.append('0');
                }
                sb.append(digits);
            }
        } else {
            sb.append(digits.charAt(0)).append('.');
            sb.append(nd > 1 ? digits.substring(1) : "0");
            sb.append('E').append(exp10);
        }
        return sb.toString();
    }
}
