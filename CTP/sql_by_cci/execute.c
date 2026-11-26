/**
 * Copyright (c) 2016, Search Solution Corporation. All rights reserved.

 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *   * Redistributions of source code must retain the above copyright notice,
 *     this list of conditions and the following disclaimer.
 *
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in
 *     the documentation and/or other materials provided with the distribution.
 *
 *   * Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products
 *     derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
 * USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <iconv.h>
#include <ctype.h>
#include <strings.h>
#include <string.h>
#include <stdbool.h>
#include <strings.h>
#include <math.h>
#include <cas_cci.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdlib.h>
#include <dirent.h>
#include <time.h>
#include <string.h>
#include <assert.h>
#include <sys/time.h>
#include <regex.h>
#if ADD_CAS_ERROR_HEADER == 1
#include <broker_cas_error.h>
#endif
#include "interface_verify.h"
#undef _GNU_SOURCE

#define DBMS_OUTPUT_BUFFER_SIZE (50000)
#define MAX_DBMS_OUTPUT_BUFFER_SIZE (1024 * 1024)  /* 1MB */
#define MAXLINELENGH 1024*1024*5
#define MAX_SQL_NUM 100*256
#define MAX_SQL_LEN 1024*200
#define MAX_LEN 1024

typedef struct SqlStateStruct
{
  char *sql;
  // query plan
  struct {
    bool hasqp; 
    bool onlyjg; /*join graph without queryplan */
    bool hasfullp;
  };

  bool iscallwithoutvalue;
} SqlStateStruce;

extern int is_statement_end ();
extern int is_in_plcsql_text ();
extern void clear_line_scanner_state ();
extern void scan_line (const char *line);

static char host[32] = "localhost";
static char user[32] = "dba";
static char passwd[32] = "";
static char url[256] = "";

static char *dbname = NULL;
static char *resname = NULL;
static char *answername = NULL;
static char *summarylog = NULL;

static int port = 0;
static int total_sql = 0;
static int queryplan = 0;
static int has_st = 0;		//add by charlie for format the show trace

static char *parameter[MAX_SQL_NUM];
static FILE *result_recorder = NULL;

static SqlStateStruce sqlstate[MAX_SQL_NUM];

static bool is_server_message_on = 0;

#ifndef CCI_ER_NOT_BIND
#define CCI_ER_NOT_BIND -20011
#endif
#define JDBC_ER_NOT_BIND -21007
#define JDBC_ER_NOT_BIND_MSG "Attempt to execute the query when not all the parameters are binded"

/*
 * CCI refuses a statement whose parameters are not all bound with CCI_ER_NOT_BIND (-20011, APIS-1143),
 * where JDBC gives -21007. Print the error the way the JDBC answer files have it.
 */
static void
map_not_bind_error (T_CCI_ERROR * error)
{
  if (error->err_code == CCI_ER_NOT_BIND)
    {
      error->err_code = JDBC_ER_NOT_BIND;
      snprintf (error->err_msg, sizeof (error->err_msg), "%s", JDBC_ER_NOT_BIND_MSG);
    }
}

/* the statement being run, for the checks that depend on its text */
static const char *current_sql = NULL;

/*
 * ConsoleBO.isPropOn/isPropOff: "<prop>\s+on" or "<prop>\s+off" found anywhere in the statement, in
 * any case. cqt takes such a statement as the command and does not run it, even when the words are in
 * a comment of the statement.
 */
static int
has_prop (const char *sql, const char *prop, const char *val)
{
  size_t pl = strlen (prop), vl = strlen (val);
  const char *p;
  for (p = sql; *p; p++)
    {
      const char *q;
      if (strncasecmp (p, prop, pl) != 0)
	continue;
      q = p + pl;
      if (!isspace ((unsigned char) *q))
	continue;
      while (isspace ((unsigned char) *q))
	q++;
      if (strncasecmp (q, val, vl) == 0)
	return 1;
    }
  return 0;
}

/* Sql.isPrep of cqt: a '?' outside quotes */
static int
is_prep (const char *sql)
{
  int lock = 1;
  for (; *sql; sql++)
    {
      if (*sql == '\'')
	lock = !lock;
      if (*sql == '?' && lock)
	return 1;
    }
  return 0;
}

/*
 * cqt asks for the plan of a statement in a .queryPlan case only when its text starts with SELECT
 * (ConsoleDAO: script.trim().toUpperCase().startsWith("SELECT")), so EXECUTE, SHOW, WITH and a
 * statement that starts with '(' or a comment get no plan. Do the same, so the answers agree.
 */
static int
starts_with_select (const char *sql)
{
  if (sql == NULL)
    {
      return 0;
    }
  while (*sql == ' ' || *sql == '\t' || *sql == '\r' || *sql == '\n')
    {
      sql++;
    }
  return strncasecmp (sql, "SELECT", 6) == 0;
}

char *
get_err_msg (int err_code)
{
  static char err_msg[1024];
  err_msg[0] = 0x00;
  cci_get_err_msg (err_code, err_msg, sizeof (err_msg));
  return err_msg;
}

int
len (char a[])
{
  int temp = 0, i;

  for (i = 0; a[i] != '\0'; i++)
    {
      temp++;
    }

  return temp;
}

int
chrindex (char a[], char b[])
{
  int i, j, temp;

  for (i = 0; i < len (a) - len (b); i++)
    {
      temp = i;
      j = 0;
      while (j <= len (b) && a[temp] == b[j])
	{
	  temp++;
	  j++;
	}

      if (j == len (b))
	return i;
    }
  return -1;
}

int
mkdir_r (const char *path, const char *res)
{
  if (path == NULL)
    {
      return -1;
    }

  char *temp = strdup (path);
  char *pos = temp;
  char *str = NULL;
  char *tmp = NULL;
  pos = pos + strlen (res);

  if (strncmp (temp, "/", 1) == 0)
    {
      pos += 1;
    }
  else if (strncmp (temp, "./", 2) == 0)
    {
      pos += 2;
    }

  for (; *pos != '\0'; ++pos)
    {
      if (*pos == '/')
	{
	  int t = pos - temp;
	  tmp = malloc (t + 1);
	  memset (tmp, 0, t + 1);
	  strncpy (tmp, temp, t);
	  *pos = '\0';
	  if (access (tmp, F_OK) != 0)
	    {
	      mkdir (tmp, 0755);
	    }
	  *pos = '/';
	  if (tmp != NULL)
	    free (tmp);
	}
    }

  free (temp);

  return 0;
}

int
copyfile (char *src, char *dest)
{
  int ch;

  FILE *psrc = fopen (src, "r");
  if (psrc == NULL)
    {
      printf ("open %s error !\n", src);
      return -1;
    }

  FILE *pdest = fopen (dest, "w+");
  if (pdest == NULL)
    {
      printf ("open %s error !\n", dest);
      return -1;
    }

  while ((ch = getc (psrc)) != EOF)
    {
      fputc (ch, pdest);
    }
  fclose (psrc);
  fclose (pdest);

  return 0;
}


void
init_log (const char *log_path)
{
  char *log_name = "/summary.info";
  int len = strlen (log_path) + strlen (log_name);
  summarylog = malloc (sizeof (char) * (len + 1));
  memset (summarylog, 0, (len + 1));
  sprintf (summarylog, "%s%s", log_path, log_name);

  if (NULL == (result_recorder = fopen (summarylog, "a+")))
    {
      perror ("Open log error");
      exit (-1);
    }
}

void
close_log ()
{
  if (fclose (result_recorder) != 0)
    {
      perror ("Close log error");
      exit (-1);
    }
}

int
isdouble (char *buffer)
{
  int len = strlen (buffer);
  int dotcount = 0, i = 1;
  if (!(buffer[0] == '-' || (buffer[0] >= '0' && buffer[0] <= '9')))
    return 0;

  for (i = 1; i < len; i++)
    {
      if (!(buffer[i] == '.' || (buffer[i] >= '0' && buffer[i] <= '9')))
	return 0;
      if (buffer[i] == '.')
	dotcount++;
      if (dotcount > 1)
	return 0;
    }
  return 1;
}

/*
 * Whether the decimal digits[0].digits[1..n-1] x 10^exp10 reads back as v > 0 (as a float when is_float).
 * strtod/strtof round correctly (half to even), so this tells whether the decimal is in R below.
 */
static int
java_number_rounds_to (const char *digits, int n, int exp10, double v, int is_float)
{
  char buf[64];

  snprintf (buf, sizeof (buf), "%c.%.*se%d", digits[0], n > 1 ? n - 1 : 1, n > 1 ? digits + 1 : "0", exp10);
  return is_float ? (strtof (buf, NULL) == (float) v) : (strtod (buf, NULL) == v);
}

/*
 * The decimal of n digits closest to v (|v|, all its exact digits in all[]) that reads back as v,
 * into out[] (n digits) and *out_exp10. Only the two decimals of n digits around v can: all[]
 * cut to n digits, and that plus one in the last digit. Returns 0 when neither does.
 */
static int
java_number_pick (const char *all, int exp10, int n, double v, int is_float, char *out, int *out_exp10)
{
  char down[32], up[32];
  int len = strlen (all), exact = 1, down_ok, up_ok = 0, up_exp10 = exp10, cmp, i;

  for (i = 0; i < n; i++)
    {
      down[i] = i < len ? all[i] : '0';
    }
  down[n] = '\0';
  for (i = n; i < len; i++)
    {
      if (all[i] != '0')
	{
	  exact = 0;
	  break;
	}
    }

  down_ok = java_number_rounds_to (down, n, exp10, v, is_float);
  if (!exact)
    {
      memcpy (up, down, n + 1);
      for (i = n - 1; i >= 0 && up[i] == '9'; i--)
	{
	  up[i] = '0';
	}
      if (i >= 0)
	{
	  up[i]++;
	}
      else
	{
	  /* 99..9 + 1 is 10^n: 1 followed by zeros, one place up */
	  up[0] = '1';
	  up_exp10 = exp10 + 1;
	}
      up_ok = java_number_rounds_to (up, n, up_exp10, v, is_float);
    }

  if (down_ok && up_ok)
    {
      /* the closer one; at the half, the one with the even last digit */
      cmp = all[n] > '5' ? 1 : (all[n] < '5' ? -1 : 0);
      for (i = n + 1; cmp == 0 && i < len; i++)
	{
	  if (all[i] != '0')
	    {
	      cmp = 1;
	    }
	}
      if (cmp == 0)
	{
	  cmp = ((down[n - 1] - '0') % 2 == 0) ? -1 : 1;
	}
      down_ok = cmp < 0;
      up_ok = !down_ok;
    }
  if (down_ok)
    {
      memcpy (out, down, n + 1);
      *out_exp10 = exp10;
      return 1;
    }
  if (up_ok)
    {
      memcpy (out, up, n + 1);
      *out_exp10 = up_exp10;
      return 1;
    }
  return 0;
}

/*
 * The text Java gives a float or a double with Float.toString/Double.toString since JDK 19
 * (JDK-4511638), which cqt prints with JavaNumberFormat whatever its JDK (APIS-1143). From the
 * specification in the JDK 19 javadoc: of the decimals that round to v (R), take those of the
 * least length m (of length 1 or 2 when m is 1), and of them the one closest to v (of two, the one
 * with the even last digit). It is written plain when 1e-3 <= |v| < 1e7 ("111.26", "0.001",
 * "1234567.0") and as d.dddEn otherwise ("1.0E7", "1.5E-10").
 */
void
java_number_str (char *out, size_t out_size, double v, int is_float)
{
  /* the exact decimal expansion of a double has at most 767 significant digits */
  char exact[1100], all[1100], digits[32];
  int exp10, nd, i, k, n;
  char *e;

  if (isnan (v))
    {
      snprintf (out, out_size, "NaN");
      return;
    }
  if (isinf (v))
    {
      snprintf (out, out_size, "%sInfinity", v < 0 ? "-" : "");
      return;
    }
  if (v == 0)
    {
      snprintf (out, out_size, "%s0.0", signbit (v) ? "-" : "");
      return;
    }

  /* exact[] is d.ddd...e[+-]xx with all the digits of |v| (glibc prints a double exactly) */
  snprintf (exact, sizeof (exact), "%.800e", fabs (v));
  e = strchr (exact, 'e');
  exp10 = atoi (e + 1);
  k = 0;
  for (i = 0; exact + i < e; i++)
    {
      if (exact[i] != '.')
	{
	  all[k++] = exact[i];
	}
    }
  all[k] = '\0';

  for (n = 1; n <= 17; n++)
    {
      if (java_number_pick (all, exp10, n, fabs (v), is_float, digits, &k))
	{
	  break;
	}
    }
  if (n == 1)
    {
      /* m is 1: the closest of length 1 or 2, which is the closest of length 2 */
      java_number_pick (all, exp10, 2, fabs (v), is_float, digits, &k);
    }
  exp10 = k;

  k = strlen (digits);
  while (k > 1 && digits[k - 1] == '0')
    {
      digits[--k] = '\0';
    }
  nd = k;

  i = 0;
  if (v < 0)
    {
      out[i++] = '-';
    }
  if (exp10 >= -3 && exp10 < 7)
    {
      if (exp10 >= 0)
	{
	  for (k = 0; k <= exp10; k++)
	    {
	      out[i++] = k < nd ? digits[k] : '0';
	    }
	  out[i++] = '.';
	  if (nd > exp10 + 1)
	    {
	      for (k = exp10 + 1; k < nd; k++)
		{
		  out[i++] = digits[k];
		}
	    }
	  else
	    {
	      out[i++] = '0';
	    }
	}
      else
	{
	  out[i++] = '0';
	  out[i++] = '.';
	  for (k = 0; k < -exp10 - 1; k++)
	    {
	      out[i++] = '0';
	    }
	  for (k = 0; k < nd; k++)
	    {
	      out[i++] = digits[k];
	    }
	}
      out[i] = '\0';
    }
  else
    {
      out[i++] = digits[0];
      out[i++] = '.';
      if (nd > 1)
	{
	  for (k = 1; k < nd; k++)
	    {
	      out[i++] = digits[k];
	    }
	}
      else
	{
	  out[i++] = '0';
	}
      snprintf (out + i, out_size - i, "E%d", exp10);
    }
}

/*
 * A BIT read as a boolean, the way JDBC reads a BIT(8): 1 when its first byte is not 0. A CCI with
 * CCI_A_TYPE_INT for a BIT (APIS-1143) does it; an older one gives CCI_ER_TYPE_CONVERSION, and the
 * first byte is then taken from CCI_A_TYPE_BIT.
 */
int
get_bit_as_bool (int req, int col, int *value, int *ind)
{
  T_CCI_BIT bit;
  int res;

  res = cci_get_data (req, col, CCI_A_TYPE_INT, value, ind);
  if (res != CCI_ER_TYPE_CONVERSION)
    {
      return res;
    }
  res = cci_get_data (req, col, CCI_A_TYPE_BIT, &bit, ind);
  if (res >= 0 && *ind >= 0)
    {
      *value = (bit.size > 0 && bit.buf[0] != 0) ? 1 : 0;
    }
  return res;
}

/* the charset codes of T_CCI_COL_INFO.charset that the JDBC driver maps in UJCIUtil.getJavaCharsetName() */
#define CCI_CS_ASCII     0
#define CCI_CS_BINARY    2
#define CCI_CS_ISO8859_1 3
#define CCI_CS_EUC_KR    4
#define CCI_CS_UTF8      5

static void
put_replacement (FILE * fp)
{
  fputs ("\xEF\xBF\xBD", fp);	/* U+FFFD in UTF-8 */
}

/*
 * EUC-KR as the JDK EUC_KR decoder (sun.nio.cs.ext.DoubleByte) reads it, in UTF-8. A pair that
 * KS X 1001 maps is its character (glibc iconv). Otherwise U+FFFD, for both bytes only when the
 * first leads a row that has a character and the second is not a single byte and leads no such row
 * (DoubleByte.Decoder.crMalformedOrUnmappable), else for the first byte alone.
 */
static iconv_t euckr_cd = (iconv_t) - 1;
static char euckr_lead[256];

static int
euckr_pair (unsigned char a, unsigned char b, char *out, size_t *out_len)
{
  char in[2], u4[8];
  char *ip = in, *op = u4;
  size_t il = 2, ol = sizeof (u4);
  unsigned long cp;

  in[0] = (char) a;
  in[1] = (char) b;
  iconv (euckr_cd, NULL, NULL, NULL, NULL);
  /* exactly one character for the two bytes */
  if (iconv (euckr_cd, &ip, &il, &op, &ol) == (size_t) - 1 || il != 0 || op - u4 != 4)
    {
      return 0;
    }
  cp = ((unsigned long) (unsigned char) u4[0] << 24) | ((unsigned char) u4[1] << 16) | ((unsigned char) u4[2] << 8)
    | (unsigned char) u4[3];
  if (cp < 0x800)
    {
      out[0] = (char) (0xC0 | (cp >> 6));
      out[1] = (char) (0x80 | (cp & 0x3F));
      *out_len = 2;
    }
  else
    {
      out[0] = (char) (0xE0 | (cp >> 12));
      out[1] = (char) (0x80 | ((cp >> 6) & 0x3F));
      out[2] = (char) (0x80 | (cp & 0x3F));
      *out_len = 3;
    }
  return 1;
}

static int
put_euckr (FILE * fp, const unsigned char *p, int n)
{
  char u[8];
  size_t ul;
  int x, y;

  if (euckr_cd == (iconv_t) - 1)
    {
      euckr_cd = iconv_open ("UCS-4BE", "EUC-KR");
      for (x = 0x80; x < 0x100 && euckr_cd != (iconv_t) - 1; x++)
	for (y = 0x80; y < 0x100 && !euckr_lead[x]; y++)
	  euckr_lead[x] = (char) euckr_pair ((unsigned char) x, (unsigned char) y, u, &ul);
    }
  if (n >= 2 && euckr_cd != (iconv_t) - 1 && euckr_pair (p[0], p[1], u, &ul))
    {
      fwrite (u, 1, ul, fp);
      return 2;
    }
  put_replacement (fp);
  return (n >= 2 && euckr_lead[p[0]] && p[1] >= 0x80 && !euckr_lead[p[1]]) ? 2 : 1;
}

/* the length of the valid UTF-8 prefix of the sequence at p (at most n bytes), and whether it is complete */
static int
utf8_prefix (const unsigned char *p, int n, int *complete)
{
  int need, i;
  unsigned char lo = 0x80, hi = 0xBF;

  *complete = 0;
  if (p[0] < 0x80)
    {
      *complete = 1;
      return 1;
    }
  if (p[0] >= 0xC2 && p[0] <= 0xDF)
    need = 1;
  else if (p[0] >= 0xE0 && p[0] <= 0xEF)
    {
      need = 2;
      lo = p[0] == 0xE0 ? 0xA0 : 0x80;
      hi = 0xBF;		/* ED A0..BF is a surrogate: JDK 8 takes the sequence as one malformed one */
    }
  else if (p[0] >= 0xF0 && p[0] <= 0xF4)
    {
      need = 3;
      lo = p[0] == 0xF0 ? 0x90 : 0x80;
      hi = p[0] == 0xF4 ? 0x8F : 0xBF;
    }
  else
    return 1;			/* not a lead byte: replaced alone */

  for (i = 1; i <= need; i++)
    {
      if (i >= n)
	return i;
      if (i == 1 ? (p[i] < lo || p[i] > hi) : (p[i] < 0x80 || p[i] > 0xBF))
	return i;
    }
  *complete = !(p[0] == 0xED && p[1] >= 0xA0);
  return need + 1;
}

/*
 * A string the way cqt prints it: the JDBC driver gives a string of a BINARY charset column as
 * CUBRIDBinaryString ("%02X " for every byte), and decodes any other into a Java String with the
 * charset of the column, putting U+FFFD for every byte sequence that is not valid there; cqt then
 * writes the String in UTF-8. The length is taken from CCI, so a string that holds a NUL is printed
 * whole, as the JDBC driver gives it.
 */
void
print_java_string (FILE * fp, const char *value, int len, int charset)
{
  const unsigned char *p = (const unsigned char *) value;
  int i, n, complete;

  if (charset == CCI_CS_BINARY)
    {
      for (i = 0; i < len; i++)
	{
	  fprintf (fp, "%02X ", p[i]);
	}
      return;
    }

  for (i = 0; i < len; i += n)
    {
      if (p[i] < 0x80)
	{
	  fputc (p[i], fp);
	  n = 1;
	}
      else if (charset == CCI_CS_ISO8859_1)
	{
	  fputc (0xC0 | (p[i] >> 6), fp);
	  fputc (0x80 | (p[i] & 0x3F), fp);
	  n = 1;
	}
      else if (charset == CCI_CS_ASCII)
	{
	  put_replacement (fp);
	  n = 1;
	}
      else if (charset == CCI_CS_EUC_KR)
	{
	  n = put_euckr (fp, p + i, len - i);
	}
      else
	{
	  n = utf8_prefix (p + i, len - i, &complete);
	  if (complete)
	    {
	      fwrite (p + i, 1, n, fp);
	    }
	  else
	    {
	      put_replacement (fp);
	    }
	}
    }
}

/* CHAR, VARCHAR, NCHAR, NCHAR VARYING, ENUM and JSON: the types the JDBC driver reads as text */
int
is_string_type (int u_type)
{
  return u_type == CCI_U_TYPE_CHAR || u_type == CCI_U_TYPE_STRING || u_type == CCI_U_TYPE_NCHAR
    || u_type == CCI_U_TYPE_VARNCHAR || u_type == CCI_U_TYPE_ENUM || u_type == CCI_U_TYPE_JSON;
}

/*
 * TIMESTAMP, DATETIME and their time zone kinds: JDBC gives them as java.sql.Timestamp. u_type is a
 * basic type: a column type from the result info has to go through CCI_GET_COLLECTION_DOMAIN() first,
 * since a type above 31 (DATETIMELTZ) comes encoded there with bit 7.
 */
int
is_timestamp_type (int u_type)
{
  return u_type == CCI_U_TYPE_TIMESTAMP || u_type == CCI_U_TYPE_DATETIME || u_type == CCI_U_TYPE_TIMESTAMPTZ
    || u_type == CCI_U_TYPE_TIMESTAMPLTZ || u_type == CCI_U_TYPE_DATETIMETZ || u_type == CCI_U_TYPE_DATETIMELTZ;
}

/*
 * A TIMESTAMP or DATETIME, with or without a time zone, the way cqt prints it: the date and time as
 * Timestamp.toString() gives them, whose fraction has no trailing zero but at least one digit
 * (".0", ".12", ".888"), then the time zone part as CCI gives it. "2000-12-31 22:59:59.000 Asia/Seoul KST"
 * becomes "2000-12-31 22:59:59.0 Asia/Seoul KST", and "2015-01-01 00:10:00" "2015-01-01 00:10:00.0".
 */
void
print_java_timestamp (FILE * fp, const char *value)
{
  const char *p = value;
  const char *frac, *zone;
  int len;

  /* "yyyy-mm-dd hh:mm:ss" is 19 characters; anything else is printed as it is */
  if (strlen (value) < 19 || value[4] != '-' || value[10] != ' ' || value[13] != ':')
    {
      fprintf (fp, "%s", value);
      return;
    }
  p = value + 19;
  fprintf (fp, "%.19s", value);
  if (*p == '.')
    {
      frac = ++p;
      while (*p >= '0' && *p <= '9')
	{
	  p++;
	}
      len = (int) (p - frac);
      while (len > 1 && frac[len - 1] == '0')
	{
	  len--;
	}
      fprintf (fp, ".%.*s", len > 0 ? len : 1, len > 0 ? frac : "0");
    }
  else
    {
      fprintf (fp, ".0");
    }
  zone = p;
  fprintf (fp, "%s", zone);
}

/*
 * An element of a collection, as cqt prints it: by the type of the elements, not by how the text
 * looks. FLOAT and DOUBLE as Float.toString/Double.toString, the TIMESTAMP and DATETIME kinds as
 * Timestamp.toString, and every other type (NUMERIC included) as CCI gives it.
 */
void
print_set_element (FILE * fp, T_CCI_SET set, int index, const char *value)
{
  int u_type = cci_set_element_type (set);
  char buf[64];
  float f;
  double d;
  int ind;

  if (u_type == CCI_U_TYPE_FLOAT && cci_set_get (set, index, CCI_A_TYPE_FLOAT, &f, &ind) >= 0 && ind >= 0)
    {
      java_number_str (buf, sizeof (buf), f, 1);
      fprintf (fp, "%s", buf);
    }
  else if ((u_type == CCI_U_TYPE_DOUBLE || u_type == CCI_U_TYPE_MONETARY)
	   && cci_set_get (set, index, CCI_A_TYPE_DOUBLE, &d, &ind) >= 0 && ind >= 0)
    {
      java_number_str (buf, sizeof (buf), d, 0);
      fprintf (fp, "%s", buf);
    }
  else if (is_timestamp_type (u_type))
    {
      print_java_timestamp (fp, value);
    }
  else if (u_type == CCI_U_TYPE_BIT || u_type == CCI_U_TYPE_VARBIT)
    {
      /* cqt prints the byte[] of a BIT element with StringUtil.toHexString: lower case */
      const char *q;
      for (q = value; *q; q++)
	fputc ((*q >= 'A' && *q <= 'F') ? *q + 32 : *q, fp);
    }
  else
    {
      fprintf (fp, "%s", value);
    }
}

int
strindex (const char *s, const char *t)
{
  const char *ps = s;
  while (*ps != '\0')
    {
      const char *pps = ps;
      const char *pt = t;
      while (*pps++ == *pt++)
	{
	  if (*pt == '\0')
	    return ps - s;
	}
      ps++;
    }
  return -1;
}

//transfer number to ?
void
trannum (char *plan)
{
  int i = 0, j = 0, k = 0;
  int length;
  char *p;
  length = strlen (plan);
  p = (char *) malloc (sizeof (char) * (length + 1));
  memcpy (p, plan, sizeof (char) * length);
  p[length] = 0;
  memset (plan, 0, sizeof (char) * length);
  while (i < length)
    {
      if (p[i] >= '0' && p[i] <= '9')
	{
	  if (p[i + 1] >= '0' && p[i + 1] <= '9')
	    {
	      i++;
	      continue;
	    }
	  else
	    {
	      plan[j] = '?';
	      j++;
	    }
	}
      else
	{
	  plan[j] = p[i];
	  j++;
	}
      i++;
    }
  free (p);
}

char *
trimline (char *str)
{
  char *p = NULL;
  char *s = NULL;

  if (str == NULL)
    return (str);

  for (s = str; *s != '\0' && (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r'); s++)
    ;

  if (*s == '\0')
    {
      *str = '\0';
      return (str);
    }

  /* *s must be a non-white char */
  for (p = s; *p != '\0'; p++)
    ;

  for (p--; *p == ' ' || *p == '\t' || *p == '\n' || *p == '\r'; p--)
    ;

  *++p = '\0';
  if (s != str)
    {
      memmove (str, s, (strlen (s) + 1) * sizeof (char));
    }
  return (str);
}

void
trimbit (char *str)
{
  int i, j;
  i = strlen (str);

  for (j = 0; j < i; j++)
    {
      if (str[j] >= 'A' && str[j] <= 'F')
	{
	  str[j] += 32;
	}
    }
}

void 
replace_substring(char *source, const char *pattern, const char *replacement)
{
    char *buffer = NULL;
    char *cursor = source;
    int pattern_len = 0;
    int replacement_len = strlen(replacement);
    regex_t regex;
    regmatch_t match;

    if (regcomp(&regex, pattern, REG_EXTENDED) != 0) 
      {
        printf("Could not compile regex\n");
        return;
      }
    // Buffer size limitation.
    if (regexec(&regex, cursor, 1, &match, 0) == 0)
     {
        pattern_len = match.rm_eo - match.rm_so;
        if ( pattern_len < replacement_len)
          {
            printf("The replacement size should be smaller that the pattern size.\n");
            return;
          }
     }
    
    buffer = (char *) malloc (sizeof (char) * (strlen (source) + 1)); 
    memset (buffer, 0x00, sizeof (char) * (strlen (source) + 1)); 

    while (regexec(&regex, cursor, 1, &match, 0) == 0) 
     {
        strncat(buffer, cursor, match.rm_so);
        strcat(buffer, replacement);
        cursor += match.rm_eo;
     }

    strcat(buffer, cursor);
    strcpy(source, buffer);
    
    free (buffer); 
    regfree(&regex);
}


int
endswithsemicolon (char *source)
{
  int i = 0;

  if (source == NULL)
    return 0;

  i = strlen (source);
  if (source[i - 1] == ';')
    return 1;

  return 0;
}

int
startswith (char *source, char *str)
{
  int ret;
  ret = strncmp (source, str, strlen (str));
  return ((ret == 0) ? 1 : 0);
}

int
startswithCI (char *source, char *str)
{
  int ret;
  ret = strncasecmp (source, str, strlen (str));
  return ((ret == 0) ? 1 : 0);
}

/*
 * The parameters of a statement bound as cqt binds them (SQLParser.getParamList, CubridUtil.getSqlType
 * and getObject, ConsoleDAO.executePrepareStatement and executeCall). The types cqt knows, by the
 * whole name, upper case; any other name (NUMERIC[6,4], DATETIME, BIGINT, CHAR(10) ...) is OTHER.
 */
enum { JT_CHAR, JT_VARCHAR, JT_BIT, JT_NUMERIC, JT_INTEGER, JT_SMALLINT, JT_FLOAT, JT_DOUBLE, JT_DATE, JT_TIME,
  JT_TIMESTAMP, JT_NULL, JT_OTHER };

static int
jsql_type (const char *name)
{
  static const struct { const char *n; int t; } m[] = {
    {"CHAR", JT_CHAR}, {"VARCHAR", JT_VARCHAR}, {"STRING", JT_VARCHAR}, {"NCHAR", JT_CHAR}, {"BIT", JT_BIT},
    {"BIT VARYING", JT_BIT}, {"NUMERIC", JT_NUMERIC}, {"DECIMAL", JT_NUMERIC}, {"INTEGER", JT_INTEGER},
    {"INT", JT_INTEGER}, {"SMALLINT", JT_SMALLINT}, {"MONETARY", JT_VARCHAR}, {"FLOAT", JT_FLOAT},
    {"REAL", JT_FLOAT}, {"DOUBLE PRECISION", JT_DOUBLE}, {"DOUBLE", JT_DOUBLE}, {"DATE", JT_DATE},
    {"TIME", JT_TIME}, {"TIMESTAMP", JT_TIMESTAMP}, {"NULL", JT_NULL}
  };
  size_t i;
  if (*name == '\0')
    return JT_VARCHAR;
  for (i = 0; i < sizeof (m) / sizeof (m[0]); i++)
    if (strcasecmp (name, m[i].n) == 0)
      return m[i].t;
  return JT_OTHER;
}

/* Integer.parseInt: an optional sign and digits only */
static int
java_parse_int (const char *s, long *out)
{
  const char *p = s;
  if (*p == '+' || *p == '-')
    p++;
  if (*p == '\0')
    return 0;
  for (; *p; p++)
    if (!isdigit ((unsigned char) *p))
      return 0;
  *out = strtol (s, NULL, 10);
  return 1;
}

static int
java_digits_part (const char *s, int from, int to, long *out)
{
  char b[64];
  if (to - from <= 0 || to - from >= (int) sizeof (b))
    return 0;
  memcpy (b, s + from, to - from);
  b[to - from] = '\0';
  return java_parse_int (b, out);
}

static int
index_of (const char *s, char c, int from)
{
  const char *p;
  if (from < 0 || from > (int) strlen (s))
    return -1;
  p = strchr (s + from, c);
  return p ? (int) (p - s) : -1;
}

/* java.sql.Date.valueOf */
static int
java_date_valueof (const char *s, long *y, long *m, long *d)
{
  int n = strlen (s), d1 = index_of (s, '-', 0), d2 = index_of (s, '-', d1 + 1);
  if (d1 > 0 && d2 > 0 && d2 < n - 1 && d1 == 4 && d2 - d1 - 1 >= 1 && d2 - d1 - 1 <= 2 && n - d2 - 1 >= 1
      && n - d2 - 1 <= 2 && java_digits_part (s, 0, d1, y) && java_digits_part (s, d1 + 1, d2, m)
      && java_digits_part (s, d2 + 1, n, d) && *m >= 1 && *m <= 12 && *d >= 1 && *d <= 31)
    return 1;
  return 0;
}

/* java.sql.Time.valueOf */
static int
java_time_valueof (const char *s, long *h, long *mi, long *se)
{
  int n = strlen (s), c1 = index_of (s, ':', 0), c2 = index_of (s, ':', c1 + 1);
  return c1 > 0 && c2 > 0 && c2 < n - 1 && java_digits_part (s, 0, c1, h) && java_digits_part (s, c1 + 1, c2, mi)
    && java_digits_part (s, c2 + 1, n, se);
}

/* java.sql.Timestamp.valueOf: yyyy-[m]m-[d]d hh:mm:ss[.f...] */
static int
java_timestamp_valueof (const char *src, long f[6], long *nanos)
{
  char s[256], ds[128], ts[128];
  int sp, n, p;
  strncpy (s, src, sizeof (s) - 1);
  s[sizeof (s) - 1] = '\0';
  trimline (s);
  sp = index_of (s, ' ', 0);
  if (sp <= 0 || sp >= (int) sizeof (ds))
    return 0;
  memcpy (ds, s, sp);
  ds[sp] = '\0';
  snprintf (ts, sizeof (ts), "%s", s + sp + 1);
  if (!java_date_valueof (ds, &f[0], &f[1], &f[2]))
    return 0;
  n = strlen (ts);
  {
    int c1 = index_of (ts, ':', 0), c2 = index_of (ts, ':', c1 + 1);
    if (!(c1 > 0 && c2 > 0 && c2 < n - 1))
      return 0;
    p = index_of (ts, '.', c2 + 1);
    if (!java_digits_part (ts, 0, c1, &f[3]) || !java_digits_part (ts, c1 + 1, c2, &f[4]))
      return 0;
    *nanos = 0;
    if (p > 0 && p < n - 1)
      {
	int k, len = n - p - 1;
	if (len > 9 || !java_digits_part (ts, c2 + 1, p, &f[5]))
	  return 0;
	for (k = p + 1; k < n; k++)
	  if (!isdigit ((unsigned char) ts[k]))
	    return 0;
	*nanos = strtol (ts + p + 1, NULL, 10);
	for (k = len; k < 9; k++)
	  *nanos *= 10;
      }
    else if (p > 0)
      return 0;
    else if (!java_digits_part (ts, c2 + 1, n, &f[5]))
      return 0;
  }
  return 1;
}

/* the fields of a java.util.Date built leniently from these (2010-02-31 is 2010-03-03), as the JDBC driver sends them */
static void
lenient (T_CCI_DATE * d, long y, long mo, long da, long h, long mi, long se, long ms)
{
  struct tm tm;
  time_t t;
  memset (&tm, 0, sizeof (tm));
  tm.tm_year = y - 1900;
  tm.tm_mon = mo - 1;
  tm.tm_mday = da;
  tm.tm_hour = h;
  tm.tm_min = mi;
  tm.tm_sec = se;
  tm.tm_isdst = -1;
  t = mktime (&tm);
  localtime_r (&t, &tm);
  memset (d, 0, sizeof (*d));
  d->yr = tm.tm_year + 1900;
  d->mon = tm.tm_mon + 1;
  d->day = tm.tm_mday;
  d->hh = tm.tm_hour;
  d->mm = tm.tm_min;
  d->ss = tm.tm_sec;
  d->ms = ms;
}

/*
 * Binds the values of a line "$type, $value, ..." to req. The line is split as cqt splits it, at a
 * comma that spaces and a '$' follow, so a value may hold a comma. A value "null" (any case) or the
 * type NULL binds a NULL (setNull).
 *  - a statement (is_call 0), as executePrepareStatement: a value with an IN: or OUT: prefix is not
 *    bound; CHAR, VARCHAR (MONETARY) as a string, NUMERIC and DOUBLE as a double, INT, SMALLINT,
 *    FLOAT by their type, DATE, TIME, TIMESTAMP through Date/Time/Timestamp.valueOf (a TIMESTAMP goes
 *    as a DATETIME, as the driver sends a java.sql.Timestamp), BIT and OTHER as a string (setObject
 *    of a String);
 *  - a CALL (is_call 1), as executeCall: setObject of the value (DATE, TIME and TIMESTAMP stay
 *    strings); a value with an OUT prefix is registered, and its position goes to outs.
 * Returns 1, or -1 when cqt fails before it executes (valueOf throws, cqt prints Error:-10000).
 * A value that CCI does not take is left unbound, so that cci_execute() refuses the statement.
 */
static int
bind_parameters (int req, const char *param_line, int is_call, int *outs, int *n_outs)
{
  char line[MAX_SQL_LEN];
  char *parts[512];
  int np = 0, i, len;
  char *p, *start;

  if (param_line == NULL)
    {
      return 1;
    }
  snprintf (line, sizeof (line), "%s", param_line);
  len = strlen (line);
  if (len > 0 && line[len - 1] == ';')
    line[--len] = '\0';
  /* split by ",( )*\$" */
  start = line;
  for (p = line; *p && np < 510; p++)
    {
      if (*p == ',')
	{
	  char *q = p + 1;
	  while (*q == ' ')
	    q++;
	  if (*q == '$')
	    {
	      *p = '\0';
	      parts[np++] = start;
	      start = q + 1;
	      p = q;
	    }
	}
    }
  parts[np++] = start;
  if (np % 2 != 0)
    parts[np++] = "";		/* "..., $" at the end: an empty value */
  if (parts[0][0] == '$')
    parts[0]++;

  for (i = 0; i + 1 < np; i += 2)
    {
      char tn[256], *colon, *ptype = NULL;
      const char *v = parts[i + 1];
      int idx = i / 2 + 1, jt, isnull, res = 0, k;

      snprintf (tn, sizeof (tn), "%s", parts[i]);
      trimline (tn);
      for (k = 0; tn[k] != '\0'; k++)
	{
	  tn[k] = (char) toupper ((unsigned char) tn[k]);
	}
      colon = strchr (tn, ':');
      if (colon)
	{
	  *colon = '\0';
	  ptype = tn;
	  jt = jsql_type (colon + 1);
	}
      else
	jt = jsql_type (tn);
      isnull = jt == JT_NULL || strcasecmp (v, "null") == 0;

      if (is_call)
	{
	  if (ptype != NULL && strncmp (ptype, "IN", 2) != 0)
	    {
	      if (strstr (ptype, "OUT") != NULL && *n_outs < 256)
		{
		  outs[(*n_outs)++] = idx;
		}
	      continue;
	    }
	  if (isnull)
	    res = cci_bind_param (req, idx, CCI_A_TYPE_STR, NULL, CCI_U_TYPE_NULL, 0);
	  else if (jt == JT_INTEGER)
	    {
	      int x = atoi (v);
	      res = cci_bind_param (req, idx, CCI_A_TYPE_INT, &x, CCI_U_TYPE_INT, CCI_BIND_PTR);
	    }
	  else if (jt == JT_SMALLINT)
	    {
	      int x = atoi (v);
	      res = cci_bind_param (req, idx, CCI_A_TYPE_INT, &x, CCI_U_TYPE_SHORT, CCI_BIND_PTR);
	    }
	  else if (jt == JT_FLOAT)
	    {
	      float x = strtof (v, NULL);
	      res = cci_bind_param (req, idx, CCI_A_TYPE_FLOAT, &x, CCI_U_TYPE_FLOAT, CCI_BIND_PTR);
	    }
	  else if (jt == JT_NUMERIC || jt == JT_DOUBLE)
	    {
	      double x = strtod (v, NULL);
	      res = cci_bind_param (req, idx, CCI_A_TYPE_DOUBLE, &x, CCI_U_TYPE_DOUBLE, CCI_BIND_PTR);
	    }
	  else
	    res = cci_bind_param (req, idx, CCI_A_TYPE_STR, (void *) v, CCI_U_TYPE_STRING, CCI_BIND_PTR);
	}
      else
	{
	  if (ptype != NULL)
	    continue;		/* executePrepareStatement binds only the parameters without IN:/OUT: */
	  if (isnull)
	    res = cci_bind_param (req, idx, CCI_A_TYPE_STR, NULL, CCI_U_TYPE_NULL, 0);
	  else if (jt == JT_CHAR || jt == JT_VARCHAR || jt == JT_BIT || jt == JT_OTHER)
	    res = cci_bind_param (req, idx, CCI_A_TYPE_STR, (void *) v, CCI_U_TYPE_STRING, CCI_BIND_PTR);
	  else if (jt == JT_NUMERIC || jt == JT_DOUBLE)
	    {
	      double x = strtod (v, NULL);
	      res = cci_bind_param (req, idx, CCI_A_TYPE_DOUBLE, &x, CCI_U_TYPE_DOUBLE, CCI_BIND_PTR);
	    }
	  else if (jt == JT_INTEGER)
	    {
	      int x = atoi (v);
	      res = cci_bind_param (req, idx, CCI_A_TYPE_INT, &x, CCI_U_TYPE_INT, CCI_BIND_PTR);
	    }
	  else if (jt == JT_SMALLINT)
	    {
	      int x = atoi (v);
	      res = cci_bind_param (req, idx, CCI_A_TYPE_INT, &x, CCI_U_TYPE_SHORT, CCI_BIND_PTR);
	    }
	  else if (jt == JT_FLOAT)
	    {
	      float x = strtof (v, NULL);
	      res = cci_bind_param (req, idx, CCI_A_TYPE_FLOAT, &x, CCI_U_TYPE_FLOAT, CCI_BIND_PTR);
	    }
	  else
	    {
	      T_CCI_DATE d;
	      long f[6] = { 0 }, nanos = 0;
	      T_CCI_U_TYPE ut;
	      if (jt == JT_DATE)
		{
		  if (!java_date_valueof (v, &f[0], &f[1], &f[2]))
		    return -1;
		  lenient (&d, f[0], f[1], f[2], 0, 0, 0, 0);
		  d.hh = d.mm = d.ss = 0;
		  ut = CCI_U_TYPE_DATE;
		}
	      else if (jt == JT_TIME)
		{
		  if (!java_time_valueof (v, &f[3], &f[4], &f[5]))
		    return -1;
		  lenient (&d, 1970, 1, 1, f[3], f[4], f[5], 0);
		  ut = CCI_U_TYPE_TIME;
		}
	      else
		{
		  if (!java_timestamp_valueof (v, f, &nanos))
		    return -1;
		  lenient (&d, f[0], f[1], f[2], f[3], f[4], f[5], nanos / 1000000);
		  ut = CCI_U_TYPE_DATETIME;
		}
	      res = cci_bind_param (req, idx, CCI_A_TYPE_DATE, &d, ut, CCI_BIND_PTR);
	    }
	}
      (void) res;
    }
  return 1;
}

/*
 * Opens a script so that a line may end with LF, CR LF or a CR alone, as cqt reads it with
 * BufferedReader.readLine(). A file written with CR line ends would otherwise be one long line.
 * The file is read into memory, every CR not followed by LF becomes LF, and the text is read back
 * through a memory stream.
 */
FILE *
open_script (const char *file_name)
{
  FILE *fp = fopen (file_name, "rb");
  char *text;
  long size, i;

  if (fp == NULL)
    {
      return NULL;
    }
  if (fseek (fp, 0, SEEK_END) != 0 || (size = ftell (fp)) < 0 || fseek (fp, 0, SEEK_SET) != 0)
    {
      rewind (fp);
      return fp;
    }
  text = (char *) malloc (size + 1);
  if (text == NULL || (long) fread (text, 1, size, fp) != size)
    {
      free (text);
      rewind (fp);
      return fp;
    }
  fclose (fp);
  for (i = 0; i < size; i++)
    {
      if (text[i] == '\r' && (i + 1 == size || text[i + 1] != '\n'))
	{
	  text[i] = '\n';
	}
    }
  text[size] = '\0';
  /*
   * The text as cqt reads it, through a UTF-8 reader: every byte sequence that is not UTF-8 becomes
   * U+FFFD (EF BF BD), by the rules of JDK 8, before it goes to the server.
   */
  {
    long j = 0, k;
    int n, complete;
    char *u = (char *) malloc (size * 3 + 1);
    if (u != NULL)
      {
	for (k = 0; k < size; k += n)
	  {
	    if ((unsigned char) text[k] < 0x80)
	      {
		u[j++] = text[k];
		n = 1;
		continue;
	      }
	    n = utf8_prefix ((const unsigned char *) text + k, (int) (size - k), &complete);
	    if (complete)
	      {
		memcpy (u + j, text + k, n);
		j += n;
	      }
	    else
	      {
		memcpy (u + j, "\xEF\xBF\xBD", 3);
		j += 3;
	      }
	  }
	u[j] = '\0';
	free (text);
	text = u;
	size = j;
      }
  }
  /* the buffer lives as long as the process; the script is read once */
  return size > 0 ? fmemopen (text, size, "r") : fmemopen (text, 1, "r");
}

int
readFile (char *fileName)
{
  FILE *sql_file;
  int sql_len = 0;
  int ascii1 = 0, ascii2 = 0;
  char line[MAX_SQL_LEN];
  char sql_buf[MAXLINELENGH];
  bool hasqp = 0, hasjg = 0, hasfullp = 0;

  //initial the total sql count.
  total_sql = 0;

  memset (sql_buf, 0, sizeof (char) * (MAXLINELENGH));
  if ((sql_file = open_script (fileName)) != NULL)
    {
      while (fgets (line, MAX_SQL_LEN, sql_file) != NULL)
	{
	  trimline (line);	// NOTE: in-line modification. line does not end with a '/n' after this line

	  if (strlen (line) == 0)
	    {
	      ;			// do nothing
	    }
	  else if (startswith (line, "--"))
	    {
	      if (startswith (line, "--@queryplan"))
		{
		  hasqp = 1;
		}
	      else if (startswith (line, "--@joingraph"))
		{
		  hasjg = 1;
		  hasqp = 1;
		}
	      else if (startswith (line, "--@fullplan"))
		{
		  hasfullp = 1;
		  hasqp = 1;
		}
	      else if (startswithCI (line, "--+ server-message") ||
		       startswithCI (line, "--+server-message") ||
		       startswithCI (line, "--+ holdcas") || startswithCI (line, "--+holdcas"))
		{
		  sqlstate[total_sql].sql = (char *) malloc (sizeof (char) * strlen (line) + 1);
		  strcpy (sqlstate[total_sql].sql, line);
		  sqlstate[total_sql].hasqp = 0;
		  sqlstate[total_sql].onlyjg = 0;
		  sqlstate[total_sql].hasfullp = 0;
		  //if script like "? = call"
		  sqlstate[total_sql].iscallwithoutvalue = 0;

		  total_sql++;
		}
	    }
	  else if (line[0] == '$')
	    {
	      parameter[total_sql] = (char *) malloc (sizeof (char) * (strlen (line) + 1));
	      strcpy (parameter[total_sql], line);
	    }
	  else
	    {
	      // statement
	      char *p = sql_buf + sql_len;
	      sql_len += strlen (line) + 1;
	      if (sql_len >= MAXLINELENGH)
		{
		  printf ("The sql statment is too long \n");
		  exit (1);
		}
	      sprintf (p, "%s\n", line);

	      scan_line (line);
	      // the following condition should be replaced with is_statement_end()
	      // but it hugely alters the test results.
	      if (endswithsemicolon (line) && !is_in_plcsql_text ())
		{
		  sqlstate[total_sql].sql = (char *) malloc (sizeof (char) * sql_len + 1);
		  strcpy (sqlstate[total_sql].sql, sql_buf);
		  sqlstate[total_sql].hasqp = hasqp;
		  sqlstate[total_sql].onlyjg = hasjg;
		  sqlstate[total_sql].hasfullp = hasfullp;
		  //if script like "? = call"
		  sqlstate[total_sql].iscallwithoutvalue = startswith (line, "?");

		  total_sql++;

		  memset (sql_buf, 0, sql_len);
		  sql_len = 0;
		  hasqp = 0;
		  hasjg = 0;
		  hasfullp = 0;
		}

	      if (is_statement_end ())
		{
		  clear_line_scanner_state ();
		}
	    }
	}
    }

  if (sql_file != NULL)
    fclose (sql_file);

  return 0;
}

void
formatplan (FILE * fp, char *plan)
{
  char *str, *p;
  int isplan = 0;
  int isstmt = 0;
  int i, planLen, newline;
  planLen = strlen (plan);
  str = (char *) malloc (sizeof (char) * (planLen + 1));
  memset (str, 0, sizeof (char) * (planLen + 1));
  p = (char *) malloc (sizeof (char) * (planLen + 1));
  memset (p, 0, sizeof (char) * (planLen + 1));
  newline = 0;
  if (plan != NULL)
    {
      for (i = 0; i < planLen; i++)
	{
	  if (plan[i] == 10)
	    {
	      strncpy (str, plan + newline, i - newline + 1);
	      strncpy (p, plan + newline, i - newline + 1);
	      str[i - newline + 1] = 0x00;
	      p[i - newline + 1] = 0x00;
	      newline = i + 1;

	      trimline (p);
	      if (strlen (p) == 0)
		{
		  continue;
		}

	      if (startswith (p, "Query plan:"))
		{
		  isplan = 1;
		  isstmt = 0;
		  fprintf (fp, "%s", str);
		  continue;
		}
	      else if (startswith (p, "Query stmt:"))
		{
		  isplan = 0;
		  isstmt = 1;
		  fprintf (fp, "%s", str);
		  continue;
		}
	      else if (startswith (p, "Trace Statistics:"))
		{
		  isplan = 0;
		  isstmt = 0;
		  fprintf (fp, "%s", str);
		  continue;
		}
	      else
		{
		  if (isplan)
		    {
		      trannum (str);
		      fprintf (fp, "%s", str);
		      continue;
		    }
		  if (isstmt == 1)
		    {
		      trannum (str);
		      fprintf (fp, "%s", str);
		      isplan = 0;
		      isstmt++;
		      continue;
		    }
		  if (isstmt == 2)
		    {
		      trannum (str);
		      if (strindex (str, "skip ORDER BY") > -1)
			{
			  fprintf (fp, "%s", str);
			  isplan = 0;
			  isstmt = 0;
			}

		      if (strindex (str, "skip GROUP BY") > -1)
			{
			  fprintf (fp, "%s", str);
			  isplan = 0;
			  isstmt = 0;
			}
		      continue;
		    }
		}
	    }
	  continue;
	}
      strncpy (str, plan + newline, i - newline + 1);
      str[i - newline + 1] = 0x00;
      fprintf (fp, "%s", str);
      free (str);
      free (p);
    }
}

void
formatjoingraph (FILE * fp, char *joingraph)
{
  char *str, *p;
  int i, joingraphLen, newline;
  int joinflag = 0; 

  if (joingraph == NULL)
    {
      return;
    }

  joingraphLen = strlen (joingraph);
  str = (char *) malloc (sizeof (char) * (joingraphLen + 1));
  p = (char *) malloc (sizeof (char) * (joingraphLen + 1));

  if (str == NULL || p == NULL)
  {
    if (str != NULL)
    {
      free(str);
    }

    if (p != NULL)
    {
      free(p);
    }
    
    fprintf(stdout, "formatjoingraph: malloc failure\n");
    return;
  }

  memset(str, 0, sizeof (char) * (joingraphLen + 1));
  memset(p, 0, sizeof (char) * (joingraphLen + 1));

  newline = 0;
  
  for (i = 0; i < joingraphLen; i++)
    {
      if (joingraph[i] == '\n')
        {
          strncpy (str, joingraph + newline, i - newline + 1);
          strncpy (p, joingraph + newline, i - newline + 1);
          str[i - newline + 1] = 0x00;
          p[i - newline + 1] = 0x00;
          newline = i + 1;

          trimline (p);
          if (strlen (p) == 0)
            {
              continue;
            }

          if (startswith (p, "Join graph"))
            {
              joinflag = 1;
              fprintf (fp, "%s", str);
              continue;
            }
          else if (startswith (p, "Query plan:"))
            {
              joinflag = 0;
              continue;
            }

          if (joinflag == 1)
            {
              // hide selectivity by rewriting it as 'sel ?'
              replace_substring (str, "sel [0-9]+\\.[0-9]+", "sel ?");
              fprintf (fp, "%s", str);
            }
        }
    }
  strncpy (str, joingraph + newline, i - newline + 1);
  str[i - newline + 1] = 0x00;
  fprintf (fp, "%s", str);

  free (str);
  free (p);
}

void
formatfullplan (FILE * fp, char *queryPlan)
{
  char *str, *p;
  int i, queryPlanLen, newline;
  int isjoingraph = 0;
  int isplan = 0;
  int isstmt = 0;

  if (queryPlan == NULL)
    {
      return;
    }

  queryPlanLen = strlen (queryPlan);
  str = (char *) malloc (sizeof (char) * (queryPlanLen + 1));
  p = (char *) malloc (sizeof (char) * (queryPlanLen + 1));

  if (str == NULL || p == NULL)
    {
      if (str != NULL)
        {
          free(str);
        }

      if (p != NULL)
        {
          free(p);
        }

      fprintf(stdout, "formatfullplan: malloc failure\n");
      return;
    }

  memset (str, 0, sizeof (char) * (queryPlanLen + 1));
  memset (p, 0, sizeof (char) * (queryPlanLen + 1));

  newline = 0;
  for (i = 0; i < queryPlanLen; i++)
    {
      if (queryPlan[i] == '\n')
        {
          strncpy (str, queryPlan + newline, i - newline + 1);
          str[i - newline + 1] = '\0';

          strncpy (p, queryPlan + newline, i - newline + 1);
          p[i - newline + 1] = '\0';
          newline = i + 1;

          trimline (p);
          if (strlen (p) == 0)
            {
              continue;
            }

          // Section Identification
          if (startswith (p, "Join graph"))
            {
              isjoingraph = 1;
              isplan = 0;
              isstmt = 0;
              fprintf (fp, "%s", str);
              continue;
            }
          else if (startswith (p, "Query plan:"))
            {
              isplan = 1;
              isjoingraph = 0;
              isstmt = 0;
              fprintf (fp, "%s", str);
              continue;
            }
          else if (startswith (p, "Query stmt:"))
            {
              isstmt = 1;
              isjoingraph = 0;
              isplan = 0;
              fprintf (fp, "%s", str);
              continue;
            }
          else if (startswith (p, "Trace Statistics:"))
            {
              isjoingraph = 0;
              isplan = 0;
              isstmt = 0;
              fprintf (fp, "%s", str);
              continue;
            }

          // Processing Based on Section
          if (isjoingraph)
            {
              replace_substring (str, "sel [0-9]+\\.[0-9]+", "sel ?");
              fprintf (fp, "%s", str);
              continue;
            }
          if (isplan)
            {
              trannum (str);
              fprintf (fp, "%s", str);
              continue;
            }
          if (isstmt == 1)
            {
              trannum (str);
              fprintf (fp, "%s", str);
              isstmt++;
              continue;
            }
          else if (isstmt == 2)
            {
              trannum (str);
              if (strindex (str, "skip ORDER BY") > -1 || strindex (str, "skip GROUP BY") > -1)
                {
                  fprintf (fp, "%s", str);
                  isstmt = 0;
                }
              continue;
            }
        }
    }
  strncpy (str, queryPlan + newline, queryPlanLen - newline);
  str[queryPlanLen - newline] = '\0';
  fprintf (fp, "%s", str);

  free (str);
  free (p);
}


int
dumptable (FILE * fp, int req, char con, bool hasqueryplan, bool onlyjoingraph, bool hasfullplan)
{
  int res = 0;
  int ind = 0, index_count = 0, col_count = 0, setsize = -1, index_set = 0;
  int u_type = 0, itemp = 0;
  static int seq2 = 0;
  void *buffer;
  char buffertemp[1024];
  float f;
  double d_value;
  void *bufferset;
  T_CCI_ERROR error;
  T_CCI_COL_INFO *res_col_info;
  T_CCI_SQLX_CMD cmd_type;
  char *plan = NULL;
  char class_str[1024] = { 0x00 };	/* a class name of 24 bytes and more was cut at 24 */

_NEXT_MULTIPLE_LINE_SQL:
  //getting column information when the prepared statement is the SELECT query
  res_col_info = cci_get_result_info (req, &cmd_type, &col_count);
  if (!res_col_info || col_count == 0)
    {
      if (cmd_type != CUBRID_STMT_SELECT && cmd_type != CUBRID_STMT_CALL)
	{
	  fprintf (fp, "%d\n", res);
	  goto _FOR_DML_STATEMENT_END;
	}
      else
	{
	  goto _DUMPTABLE_ERROR;
	}
    }

  for (index_count = 1; index_count <= col_count; index_count++)
    {
      u_type = CCI_GET_RESULT_INFO_TYPE (res_col_info, index_count);
      if (!(u_type == CCI_U_TYPE_FIRST || u_type == CCI_U_TYPE_UNKNOWN || u_type == CCI_U_TYPE_NULL))
	{
	  fprintf (fp, "%s", CCI_GET_RESULT_INFO_NAME (res_col_info, index_count));
	}
      else if (CCI_GET_RESULT_INFO_NAME (res_col_info, index_count) != NULL)
	{

	  fprintf (fp, "%s", CCI_GET_RESULT_INFO_NAME (res_col_info, index_count));
	  fprintf (stdout, "%s", CCI_GET_RESULT_INFO_NAME (res_col_info, index_count));
	}
      fprintf (fp, "    ");
      fprintf (stdout, "    ");
    }

  fprintf (stdout, "\n");
  fprintf (fp, "\n");
  res = cci_cursor (req, 1, CCI_CURSOR_FIRST, &error);
  if (res == CCI_ER_NO_MORE_DATA)
    {
      fprintf (fp, "\n");
      if ((queryplan && starts_with_select (current_sql)) || hasqueryplan)
	{
	  goto _PRINT_QUERY_PLAN;
	}
      else
	{
	  goto _DUMPTABLE_WHILE_END;
	}
    }

  if (res < 0)
    {
      fprintf (stdout, "Error:%d\n", error.err_code);
      goto _DUMPTABLE_ERROR;
    }

  res = cci_fetch (req, &error);
  if (res < 0)
    {
      fprintf (stdout, "Error:%d\n", error.err_code);
      goto _DUMPTABLE_ERROR;
    }

  while (1)
    {
      for (index_count = 1; index_count <= col_count; index_count++)
	{
	  itemp = CCI_GET_RESULT_INFO_TYPE (res_col_info, index_count);
	  if (CCI_IS_SET_TYPE (itemp) || CCI_IS_MULTISET_TYPE (itemp) || CCI_IS_SEQUENCE_TYPE (itemp)
	      || CCI_IS_COLLECTION_TYPE (itemp))
	    {
	      //trimset((char*)buffer);
	      if ((res = cci_get_data (req, index_count, CCI_A_TYPE_SET, &buffer, &ind)) < 0)
		{
		  fprintf (stdout, "Error:%d\n", error.err_code);
		  goto _DUMPTABLE_ERROR;
		}
	      if (ind < 0)
		{
		  fprintf (fp, "null");
		}
	      else
		{
		  setsize = cci_set_size (buffer);
		  for (index_set = 1; index_set <= setsize; index_set++)
		    {
		      res = cci_set_get (buffer, index_set, CCI_A_TYPE_STR, &bufferset, &ind);
		      if (res < 0)
			{
			  goto _DUMPTABLE_ERROR;
			}

		      if (ind < 0)
			{
			  fprintf (fp, "null");
			}
		      else
			{
			  if (((char *) bufferset)[0] == '@')	//if the result is oid then transfer it to characters.
			    {
			      res =
				cci_oid_get_class_name (con, (char *) bufferset, class_str, sizeof (class_str), &error);
			      if (res < 0)
				{
				  //fprintf(stdout, "(%s, %d) ERROR : %s [%d] \n\n", __FILE__, __LINE__,error.err_msg, error.err_code );
				  fprintf (fp, "null");
				}
			      fprintf (fp, "%s", class_str);
			    }
			  else
			    {
			      /* an element prints as cqt prints a column of its type */
			      print_set_element (fp, buffer, index_set, (char *) bufferset);
			    }
			}
		      fprintf (fp, ",");
		    }
		}
	      fprintf (fp, "     ");
	    }
	  else if (itemp == CCI_U_TYPE_DOUBLE || itemp == CCI_U_TYPE_MONETARY)
	    {
	      if ((res = cci_get_data (req, index_count, CCI_A_TYPE_DOUBLE, &d_value, &ind)) < 0)
		{
		  fprintf (stdout, "Error:%d\n", error.err_code);
		  goto _DUMPTABLE_ERROR;
		}
	      if (ind < 0)
		{
		  fprintf (fp, "null     ");
		}
	      else
		{
		  java_number_str (buffertemp, sizeof (buffertemp), d_value, 0);
		  fprintf (fp, "%s     ", buffertemp);
		}
	    }
	  else if (itemp == CCI_U_TYPE_BIT && CCI_GET_RESULT_INFO_PRECISION (res_col_info, index_count) == 8
		   && cmd_type != CUBRID_STMT_CALL_SP)
	    {
	      /* JDBC reads a BIT(8) as java.lang.Boolean (CUBRID has no BOOLEAN), so cqt prints true or false */
	      int bit_value = 0;

	      if ((res = get_bit_as_bool (req, index_count, &bit_value, &ind)) < 0)
		{
		  fprintf (stdout, "Error:%d\n", res);
		  goto _DUMPTABLE_ERROR;
		}
	      fprintf (fp, "%s     ", ind < 0 ? "null" : (bit_value ? "true" : "false"));
	    }
	  else if (itemp == CCI_U_TYPE_FLOAT)
	    {
	      if ((res = cci_get_data (req, index_count, CCI_A_TYPE_FLOAT, &f, &ind)) < 0)
		{
		  fprintf (stdout, "Error:%d\n", error.err_code);
		  goto _DUMPTABLE_ERROR;
		}
	      if (ind < 0)
		{
		  fprintf (fp, "null     ");
		}
	      else
		{
		  java_number_str (buffertemp, sizeof (buffertemp), f, 1);
		  fprintf (fp, "%s     ", buffertemp);
		}
	    }
	  else
	    {
	      if ((res = cci_get_data (req, index_count, CCI_A_TYPE_STR, &buffer, &ind)) < 0)
		{
		  fprintf (stdout, "Error:%d\n", error.err_code);
		  goto _DUMPTABLE_ERROR;
		}

	      if (ind < 0)
		{
		  fprintf (fp, "null     ");
		}
	      else
		{
		  if (itemp == CCI_U_TYPE_BIT || itemp == CCI_U_TYPE_VARBIT)
		    {
		      trimbit ((char *) buffer);
		    }
		  if (itemp == CCI_U_TYPE_NUMERIC)
		    {
		      /* every digit of the scale, as cqt prints it with BigDecimal.toPlainString() */
		      fprintf (fp, "%s", (char *) buffer);
		    }
		  else if (is_timestamp_type (CCI_GET_COLLECTION_DOMAIN (itemp)))
		    {
		      print_java_timestamp (fp, (char *) buffer);
		    }
		  else if (is_string_type (CCI_GET_COLLECTION_DOMAIN (itemp)) && !has_st)
		    {
		      print_java_string (fp, (char *) buffer, ind, CCI_GET_RESULT_INFO_CHARSET (res_col_info, index_count));
		    }
		  else if (itemp == CCI_U_TYPE_NULL)
		    {
		      if (((char *) buffer)[0] == '@')
			{
			  res = cci_oid_get_class_name (con, (char *) buffer, class_str, sizeof (class_str), &error);
			  if (res < 0)
			    {
			      fprintf (stdout, "(%s, %d) ERROR : %s [%d] \n\n", __FILE__, __LINE__, error.err_msg,
				       error.err_code);
			    }
			  fprintf (fp, "%s", class_str);
			}
		      else
			{
			  fprintf (fp, "%s", (char *) buffer);
			}
		    }
		  else if (itemp == CCI_U_TYPE_OBJECT)
		    {
		      res = cci_oid_get_class_name (con, (char *) buffer, class_str, sizeof (class_str), &error);
		      if (res < 0)
			{
			  //fprintf(stdout, "(%s, %d) ERROR : %s [%d] \n\n", __FILE__, __LINE__,error.err_msg, error.err_code );
			  fprintf (fp, "null");
			}
		      else
			{
			  fprintf (fp, "%s", class_str);
			}
		    }
		  else
		    {
		      if (has_st)	//add by charlie for format the show trace
			{
			  trannum ((char *) buffer);
			  has_st = 0;
			}
		      fprintf (fp, "%s", (char *) buffer);
		    }

		  fprintf (fp, "     ");
		}
	    }
	  //finish to restrive data
	  // fprintf (fp, "\n");
	  // goto _DUMPTABLE_WHILE_END;
	}
      fprintf (fp, "\n");
      res = cci_cursor (req, 1, CCI_CURSOR_CURRENT, &error);
      if (res == CCI_ER_NO_MORE_DATA)
	{
	  fprintf (fp, "\n");
	  if ((queryplan && starts_with_select (current_sql)) || hasqueryplan)
	    {
	      res = cci_get_query_plan (req, &plan);
	      {
		if (res < 0)
		  {
		    fprintf (stdout, "%s(%d) - %s ERROR : (%s %d) \n\n", __FILE__, __LINE__, __FUNCTION__,
			     get_err_msg (res), res);
		  }
		if (res >= 0)
		  {
             if (onlyjoingraph)
               {
                 formatjoingraph (fp, plan);
               }
             else if (hasfullplan)
               {
                 formatfullplan (fp, plan);
               }
             else
               {
                 formatplan (fp, plan);
               }
      }
	      }
	    }

	_FOR_DML_STATEMENT_END:
	  res = cci_next_result (req, &error);
	  if (res == CAS_ER_NO_MORE_RESULT_SET)
	    {
	      goto _DUMPTABLE_WHILE_END;
	    }
	  goto _NEXT_MULTIPLE_LINE_SQL;
	}
      if (res < 0)
	{
	  fprintf (stdout, "Error:%d\n", error.err_code);
	  goto _DUMPTABLE_ERROR;
	}
      res = cci_fetch (req, &error);
      if (res < 0)
	{
	  fprintf (stdout, "Error:%d\n", error.err_code);
	  goto _DUMPTABLE_ERROR;
	}
    }

  //release
  if (res < 0)
    {
      fprintf (stdout, "Error:%d\n", error.err_code);
      goto _DUMPTABLE_ERROR;
    }
  return 0;
_PRINT_QUERY_PLAN:
  res = cci_get_query_plan (req, &plan);
  if (res < 0)
    {
      fprintf (stdout, "%s(%d) - %s ERROR : (%s %d) \n\n", __FILE__, __LINE__, __FUNCTION__, get_err_msg (res), res);
    }
  if (res >= 0)
    {
      if (onlyjoingraph)
        {
           formatjoingraph (fp, plan);
        }
      else if (hasfullplan)
        {
           formatfullplan (fp, plan);
        }
      else
        {
           formatplan (fp, plan);
        }
    }
  goto _DUMPTABLE_WHILE_END;
_DUMPTABLE_WHILE_END:return 0;
_DUMPTABLE_ERROR:return -1;
}

static int
set_server_message (FILE * fp, char conn, bool on)
{
  char sql[20];
  int req, res = 0;
  T_CCI_ERROR error;
  
  /* if phase-1 */
  if (on)
    {
      sprintf (sql, "call DBMS_OUTPUT.enable(%d)", DBMS_OUTPUT_BUFFER_SIZE);
    }
  else
    {
      sprintf (sql, "call DBMS_OUTPUT.disable()");
    }

  req = cci_prepare (conn, sql, CCI_PREPARE_CALL, &error);
  if (req < 0)
    {
      /* if phase-0 */
      if (on)
        {
          sprintf (sql, "call enable(%d)", DBMS_OUTPUT_BUFFER_SIZE);
        }
      else
        {
          sprintf (sql, "call disable()");
        }
      req = cci_prepare (conn, sql, CCI_PREPARE_CALL, &error);
      if (req < 0)
        {
          fprintf (stdout, "Set Server-Message Error:%d\n", error.err_code);
          fprintf (fp, "Set Server-Message Error:%d\n", error.err_code);
          res = -1;
          goto _END;
	}
    }

  res = cci_execute (req, 0, 0, &error);
  if (res < 0)
    {
      fprintf (stdout, "Set Server-Message Error:%d\n", error.err_code);
      fprintf (fp, "Set Server-Message Error:%d\n", error.err_code);
      goto _END;
    }

  is_server_message_on = on;

_END:
  if (req > 0)
    {
      cci_close_req_handle (req);
    }
  return res;
}

static char *
get_server_output (FILE * fp, char conn)
{
  int req = 0, res = 0;
  T_CCI_ERROR error;
  const char *sql = "call DBMS_OUTPUT.get_line(?, ?)";
  char *ret = NULL, *buff = NULL, *p, *str;
  size_t buf_size = DBMS_OUTPUT_BUFFER_SIZE;
  int status, ind;
  
  /* allocate initial buffer */
  buff = malloc (buf_size);
  if (buff == NULL)
    {
      fprintf (stdout, "Get Server-Output Error: malloc failed\n");
      fprintf (fp, "Get Server-Output Error: malloc failed\n");
      goto _END;
    }
  memset (buff, 0, buf_size);
  buff[0] = '\n';
  buff[1] = '\0';
  p = buff + 1;

  /* if phase-1 */
  req = cci_prepare (conn, sql, CCI_PREPARE_CALL, &error);
  if (req < 0)
    {
      /* if phase-0 */
      sql = "CALL GET_LINE (?, ?)";

      req = cci_prepare (conn, sql, CCI_PREPARE_CALL, &error);
      if (req < 0)
        {
          fprintf (stdout, "Get Server-Output Error:%d\n", error.err_code);
          fprintf (fp, "Get Server-Output Error:%d\n", error.err_code);
          goto _END;
	}
    }

  res = cci_register_out_param (req, 1);
  if (res < 0)
    {
      fprintf (stdout, "Get Server-Output Error:%d\n", error.err_code);
      fprintf (fp, "Get Server-Output Error:%d\n", error.err_code);
      goto _END;
    }

  res = cci_register_out_param (req, 2);
  if (res < 0)
    {
      fprintf (stdout, "Get Server-Output Error:%d\n", error.err_code);
      fprintf (fp, "Get Server-Output Error:%d\n", error.err_code);
      goto _END;
    }

  while (1)
    {
      res = cci_execute (req, 0, 0, &error);
      if (res < 0)
	{
	  fprintf (stdout, "Get Server-Output Error:%d\n", error.err_code);
	  fprintf (fp, "Get Server-Output Error:%d\n", error.err_code);
	  goto _END;
	}

      res = cci_cursor (req, 1, CCI_CURSOR_FIRST, &error);
      if (res == CCI_ER_NO_MORE_DATA)
	{
	  fprintf (stdout, "Get Server-Output Error:%d\n", error.err_code);
	  fprintf (fp, "Get Server-Output Error:%d\n", error.err_code);
	  goto _END;
	}

      res = cci_fetch (req, &error);
      if (res < 0)
	{
	  fprintf (stdout, "Get Server-Output Error:%d\n", error.err_code);
	  fprintf (fp, "Get Server-Output Error:%d\n", error.err_code);
	  goto _END;
	}

      res = cci_get_data (req, 2, CCI_A_TYPE_INT, &status, &ind);
      if (res < 0)
	{
	  fprintf (stdout, "Get Server-Output Error:%d\n", error.err_code);
	  fprintf (fp, "Get Server-Output Error:%d\n", error.err_code);
	  goto _END;
	}

      if (ind == 0 && status == 0)
	{

	  res = cci_get_data (req, 1, CCI_A_TYPE_STR, &str, &ind);
	  if (res < 0)
	    {
	      fprintf (stdout, "Get Server-Output Error:%d\n", error.err_code);
	      fprintf (fp, "Get Server-Output Error:%d\n", error.err_code);
	      goto _END;
	    }

	  assert (ind >= 0);
	  if (ind > 0)
	    {
              size_t need = (p - buff) + ind + 2;
              if (need > buf_size)
                {
                  size_t new_size = buf_size;
                  while (new_size < need && new_size < MAX_DBMS_OUTPUT_BUFFER_SIZE)
                    new_size *= 2;
                  if (new_size >= MAX_DBMS_OUTPUT_BUFFER_SIZE)
                    {
                      fprintf (stdout, "Warning: buffer max size reached\n");
                      break;
                    }
                  size_t offset = p - buff;
                  char *tmp = realloc (buff, new_size);
                  if (tmp == NULL)
                    {
                      fprintf(stdout, "Get Server-Output Error: realloc failed\n");
                      goto _END;
                    }
                  buff = tmp;
                  if (new_size > offset)
                    {
                      memset (buff + offset, 0, new_size - offset);
                    }
                  buf_size = new_size;
                  p = buff + offset;
                }
              {
                int written = snprintf (p, buf_size - (p - buff), "%s\n", str);
                if (written < 0)
                  {
                    fprintf (stdout, "Get Server-Output Error: snprintf failed\n");
                    goto _END;
                  }
                p += written;
              }
	    }
	  else
	    {
	      strcpy (p, "\n");
	      p++;
	    }

	}
      else
	{
	  break;
	}

      res = cci_close_query_result (req, &error);
      if (res < 0)
	{
	  fprintf (stdout, "Get Server-Output Error:%d\n", error.err_code);
	  fprintf (fp, "Get Server-Output Error:%d\n", error.err_code);
	  goto _END;
	}
    }

  ret = buff;

_END:
  if (ret == NULL && buff != NULL)
    free (buff);
  if (req > 0)
    cci_close_req_handle (req);
  return ret;
}


int
execute (FILE * fp, char conn, const SqlStateStruce *pSqlState)
{
  static int seq = 0;
  int req = 0, res = 0, ret = 0;
  int execute_result = 0;
  T_CCI_ERROR error;
  int col_count = 0;
  char *plan = NULL;
  T_CCI_COL_INFO *res_col_info;
  T_CCI_SQLX_CMD cmd_type;
  char *server_output_buffer = NULL;
  char *sql = pSqlState->sql;
  bool hasqueryplan = pSqlState->hasqp;

  current_sql = sql;
  bool onlyjoingraph = pSqlState->onlyjg;
  bool hasfullplan = pSqlState->hasfullp;
  bool executed = false;

  fprintf (fp, "===================================================\n");

  req = cci_prepare (conn, sql, 0, &error);
  if (req < 0)
    {
      fprintf (stdout, "Error:%d\n", error.err_code);
      fprintf (fp, "Error:%d\n", error.err_code);
      if (is_server_message_on)
	{
	  char *end = strstr (error.err_msg, "[CAS INFO");
	  if (end)
	    {
	      *end = '\0';
	    }
	  fprintf (fp, "%s\n\n", error.err_msg);
	}
      ret = -1;
      goto _END;
    }

  res = cci_execute (req, CCI_EXEC_QUERY_ALL, 0, &error);
  executed = true;
  if (res < 0)
    {
      fprintf (stdout, "Error:%d\n", error.err_code);
      map_not_bind_error (&error);
      fprintf (fp, "Error:%d\n", error.err_code);
      if (is_server_message_on)
	{
	  char *end = strstr (error.err_msg, "[CAS INFO");
	  if (end)
	    {
	      *end = '\0';
	    }
	  fprintf (fp, "%s\n", error.err_msg);
	}
      ret = -1;
      goto _END;
    }

  //getting column information when the prepared statement is the SELECT query
  res_col_info = cci_get_result_info (req, &cmd_type, &col_count);
  if (cmd_type == CUBRID_STMT_SELECT || cmd_type == CUBRID_STMT_CALL || cmd_type == CUBRID_STMT_EVALUATE
      || cmd_type == CUBRID_STMT_GET_STATS)
    {
      dumptable (fp, req, conn, hasqueryplan, onlyjoingraph, hasfullplan);
      goto _END;
    }
  else if (cmd_type == CUBRID_STMT_UPDATE || cmd_type == CUBRID_STMT_DELETE)
    {
      fprintf (fp, "%d\n", res);
      if (hasqueryplan)
	{
	  res = cci_get_query_plan (req, &plan);
	  if (res < 0)
	    {
	      fprintf (stdout, "%s(%d) - %s ERROR : (%s %d) \n\n",
		       __FILE__, __LINE__, __FUNCTION__, get_err_msg (res), res);
	    }
	  if (res >= 0)
	    {
	      if (onlyjoingraph)
	        {
	          formatjoingraph (fp, plan);
	        }
	      else if (hasfullplan)
	        {
	          formatfullplan (fp, plan);
	        }
	      else
	        {
	          formatplan (fp, plan);
	        }
	    }
	}
    }
  else
    {
      fprintf (fp, "%d\n", res);
    }

  while (1)
    {
      res = cci_next_result (req, &error);
      if (res == CAS_ER_NO_MORE_RESULT_SET)
	break;

      if (res < 0)
	{
	  fprintf (stdout, "Error:%d\n", error.err_code);
	  fprintf (fp, "Error:%d\n", error.err_code);
	  ret = -1;
	  goto _END;
	}

      res_col_info = cci_get_result_info (req, &cmd_type, &col_count);
      if (cmd_type == CUBRID_STMT_SELECT || cmd_type == CUBRID_STMT_CALL)
	{
	  dumptable (fp, req, conn, hasqueryplan, onlyjoingraph, hasfullplan);
	}
      else
	{
	  printf ("%d\n", res);
	  fprintf (fp, "%d\n", res);
	}
    }

_END:
  if (executed && is_server_message_on)
    {
      server_output_buffer = get_server_output (fp, conn);
      if (server_output_buffer)
        {
          fprintf (fp, "%s", server_output_buffer);
        }
    }
  if (req > 0)
    cci_close_req_handle (req);
  return ret;
}

int
executebind (FILE * fp, char conn, char *param, const SqlStateStruce *pSqlState)
{
  static int seq = 0;
  int ind;
  int req = 0;
  int res = 0;
  int ret = 0;
  int execute_result = 0;
  int bound;
  int outs[256];
  int n_outs = 0;
  int i;
  T_CCI_ERROR error;
  int col_count = 0, t = 0;
  char *buffer;
  T_CCI_COL_INFO *res_col_info;
  T_CCI_SQLX_CMD cmd_type;
  char *server_output_buffer = NULL;
  char *sql = pSqlState->sql;
  bool hasqueryplan = pSqlState->hasqp;

  current_sql = sql;
  bool onlyjoingraph = pSqlState->onlyjg;
  bool hasfullplan = pSqlState->hasfullp;
  bool iscall = pSqlState->iscallwithoutvalue;
  bool executed = false;

  fprintf (fp, "===================================================\n");

  if (iscall)
    {
      req = cci_prepare (conn, sql, CCI_PREPARE_CALL, &error);
    }
  else
    {
      req = cci_prepare (conn, sql, 0, &error);
    }

  if (req < 0)
    {
      fprintf (stdout, "Error:%d\n", error.err_code);
      fprintf (fp, "Error:%d\n", error.err_code);
      if (is_server_message_on)
	{
	  char *end = strstr (error.err_msg, "[CAS INFO");
	  if (end)
	    {
	      *end = '\0';
	    }
	  fprintf (fp, "%s\n\n", error.err_msg);
	}
      ret = -1;
      goto _END;
    }

  bound = bind_parameters (req, param, iscall, outs, &n_outs);
  if (bound < 0)
    {
      /* cqt fails before it executes: Date/Time/Timestamp.valueOf() throws on the value */
      fprintf (fp, "Error:-10000\n");
      ret = -1;
      goto _END;
    }
  for (i = 0; i < n_outs; i++)
    {
      if (cci_register_out_param (req, outs[i]) < 0)
	{
	  fprintf (stdout, "register parameter error\n");
	  ret = -1;
	  goto _END;
	}
    }

  /* a value CCI did not take leaves its parameter unbound: cci_execute() then refuses, as JDBC does */
  res = cci_execute (req, CCI_EXEC_QUERY_ALL, 0, &error);
  executed = true;
  if (res < 0)
    {
      fprintf (stdout, "Error:%d\n", error.err_code);
      map_not_bind_error (&error);
      fprintf (fp, "Error:%d\n", error.err_code);
      if (is_server_message_on)
	{
	  char *end = strstr (error.err_msg, "[CAS INFO");
	  if (end)
	    {
	      *end = '\0';
	    }
	  fprintf (fp, "%s\n", error.err_msg);
	}
      ret = -1;
      goto _END;
    }

  if (iscall)
    {
      //print call statement column name
      for (t = 1; t <= n_outs; t++)
	{
	  if (t == 1)
	    {
	      fprintf (fp, "%d", n_outs);
	    }
	  else
	    {
	      fprintf (fp, " %d", n_outs);
	    }
	}
      fprintf (fp, "\n");

      //print data
      res = cci_cursor (req, 1, CCI_CURSOR_CURRENT, &error);
      if (res == CCI_ER_NO_MORE_DATA)
	{
	  fprintf (fp, "Error:%d\n", error.err_code);
	  ret = -1;
	  goto _END;
	}

      if ((res = cci_fetch (req, &error) < 0))
	{
	  fprintf (fp, "Error:%d\n", error.err_code);
	  ret = -1;
	  goto _END;
	}

      if ((res = cci_get_data (req, 1, CCI_A_TYPE_STR, &buffer, &ind)) < 0)
	{
	  fprintf (fp, "Error:%d\n", error.err_code);
	  ret = -1;
	  goto _END;
	}
      // ind: string length, buffer: a string which came from the out binding parameter of test_out(?) Java SP.
      if (ind == -1)
	{
	  fprintf (fp, "null\n");
	}
      else
	{
	  fprintf (fp, "%s\n", buffer);
	}
      ret = -1;
      goto _END;
    }

  res_col_info = cci_get_result_info (req, &cmd_type, &col_count);
  /*
   * A CALL with parameter values runs in cqt through PreparedStatement.execute(), which gives no
   * result set but an update count, so cqt prints the count (1) and not the return value. A CALL
   * without parameters runs through Statement and prints its result set, as in execute().
   */
  if (cmd_type == CUBRID_STMT_SELECT)
    {
      dumptable (fp, req, conn, hasqueryplan, onlyjoingraph, hasfullplan);
    }
  else
    {
      fprintf (fp, "%d\n", res);
      while (1)
	{
	  res = cci_next_result (req, &error);
	  if (res == CAS_ER_NO_MORE_RESULT_SET)
	    break;
	  if (res < 0)
	    {
	      fprintf (stdout, "Error:%d\n", error.err_code);
	      fprintf (fp, "Error:%d\n", error.err_code);
	      ret = -1;
	      goto _END;
	    }
	  res_col_info = cci_get_result_info (req, &cmd_type, &col_count);
	  if (cmd_type == CUBRID_STMT_SELECT || cmd_type == CUBRID_STMT_CALL)
	    {
	      dumptable (fp, req, conn, hasqueryplan, onlyjoingraph, hasfullplan);
	    }
	  else
	    {
	      fprintf (fp, "%d\n", res);
	    }
	}
    }

_END:
  if (executed && is_server_message_on)
    {
      server_output_buffer = get_server_output (fp, conn);
      if (server_output_buffer)
        {
          fprintf (fp, "%s", server_output_buffer);
        }
    }
  if (req > 0)
    cci_close_req_handle (req);
  return ret;
}

int
test (FILE * fp)
{
  int conn = -1, req = 0, res = 0;
  int sql_count = 0, length = 0, count = 0;
  int MAX_RETRY_COUNT = 50;
  T_CCI_ERROR error;

  //contect to the server until  success.
  while (conn < 0)
    {
      conn = cci_connect_with_url (url, user, passwd);
      if (conn > 0)
	{
	  break;
	}
      else if (conn < 0 && count >= MAX_RETRY_COUNT)
	{
	  fprintf (stdout, "(%s, %d) %s ERROR : cci_connect(%s %d)\n\n",
		   __FILE__, __LINE__, get_err_msg (conn), error.err_msg, error.err_code);
	  goto _END;
	}
      else
	{
	  fprintf (stdout, "CUBRID server is not available, waiting for recovery - (%s) \n", get_err_msg (conn));
	  sleep (5);
	}

      count++;
    }

  for (sql_count = 0; sql_count < total_sql; sql_count++)
    {
      if ((length = strlen (sqlstate[sql_count].sql)) <= 2)
	{
	  continue;
	}
      const char *cs = sqlstate[sql_count].sql;
      int ac_on = has_prop (cs, "autocommit", "on"), ac_off = !ac_on && has_prop (cs, "autocommit", "off");
      int hc_on = !ac_on && !ac_off && has_prop (cs, "holdcas", "on");
      int hc_off = !ac_on && !ac_off && !hc_on && has_prop (cs, "holdcas", "off");
      int sm_on = !ac_on && !ac_off && !hc_on && !hc_off && has_prop (cs, "server-message", "on");
      int sm_off = !ac_on && !ac_off && !hc_on && !hc_off && !sm_on && has_prop (cs, "server-message", "off");
      if (ac_off)
	{
	  res = cci_set_autocommit (conn, CCI_AUTOCOMMIT_FALSE);
	  if (res < 0)
	    {
	      fprintf (stdout, "(%s, %d) %s ERROR : cci_connect(%s %d)\n\n",
		       __FILE__, __LINE__, get_err_msg (conn), error.err_msg, error.err_code);
	    }
	}
      else if (ac_on)
	{
	  res = cci_set_autocommit (conn, CCI_AUTOCOMMIT_TRUE);
	  if (res < 0)
	    {
	      fprintf (stdout, "(%s, %d) %s ERROR : cci_connect(%s %d)\n\n",
		       __FILE__, __LINE__, get_err_msg (conn), error.err_msg, error.err_code);
	    }
	}
      else if (sm_on)
	{
	  set_server_message (fp, conn, 1);
	}
      else if (sm_off)
	{
	  set_server_message (fp, conn, 0);
	}
      else if (hc_on)
	{
#ifdef CCI_SET_CAS_CHANGE_MODE_INTERFACE
	  //printf("%s\n",sqlstate[j].sql);
	  res = cci_set_cas_change_mode (conn, CCI_CAS_CHANGE_MODE_KEEP, &error);
	  if (res < 0)
	    {
	      fprintf (stdout, "(%s, %d) %s ERROR : cci_set_cas_change_mode(%s %d)\n\n",
		       __FILE__, __LINE__, get_err_msg (conn), error.err_msg, error.err_code);
	    }
#else
	  fprintf (stdout, "The program doesn't compile cci_set_cas_change_mode interface.\n");
#endif
	}
      else if (hc_off)
	{
#ifdef CCI_SET_CAS_CHANGE_MODE_INTERFACE
	  res = cci_set_cas_change_mode (conn, CCI_CAS_CHANGE_MODE_AUTO, &error);
	  if (res < 0)
	    {
	      fprintf (stdout, "(%s, %d) %s ERROR : cci_set_cas_change_mode(%s %d)\n\n",
		       __FILE__, __LINE__, get_err_msg (conn), error.err_msg, error.err_code);
	    }
#else
	  fprintf (stdout, "The program doesn't compile cci_set_cas_change_mode interface.\n");
#endif
	}
      else if (startswithCI (sqlstate[sql_count].sql, "COMMIT"))
	{
	  res = cci_end_tran (conn, CCI_TRAN_COMMIT, &error);
	  if (res >= 0)
	    {
	      fprintf (fp, "===================================================\n");
	      fprintf (fp, "0\n");
	    }
	  else
	    {
	      fprintf (stdout, "(%s, %d) %s ERROR : cci_connect(%s %d)\n\n",
		       __FILE__, __LINE__, get_err_msg (conn), error.err_msg, error.err_code);
	    }
	}
      else if (startswithCI (sqlstate[sql_count].sql, "ROLLBACK"))
	{
	  char *p = NULL;
	  char *tmp = NULL;
	  int _len = 0;

	  p = sqlstate[sql_count].sql;

	  tmp = strcasestr (p, "to");
	  if (tmp != NULL && endswithsemicolon (tmp))
	    {
	      tmp[strlen (tmp) - 1] = 0;
	    }

	  if (tmp != NULL)
	    {
	      if (strcasestr (p, "savepoint") != NULL)
		{
		  _len = strlen ("to savepoint ");
		}
	      else
		{
		  _len = strlen ("to ");
		}

	      res = cci_savepoint (conn, CCI_SP_ROLLBACK, tmp + _len, &error);
	      if (res >= 0)
		{
		  fprintf (fp, "===================================================\n");
		  fprintf (fp, "0\n");
		}
	      else
		{
		  fprintf (stdout, "rollback error: %s\n", error.err_msg);
		}
	    }
	  else
	    {
	      res = cci_end_tran (conn, CCI_TRAN_ROLLBACK, &error);
	      if (res >= 0)
		{
		  fprintf (fp, "===================================================\n");
		  fprintf (fp, "0\n");
		}
	      else
		{
		  fprintf (stdout, "(%s, %d) %s ERROR : cci_connect(%s %d)\n\n",
			   __FILE__, __LINE__, get_err_msg (conn), error.err_msg, error.err_code);
		}
	    }
	}
      else if (startswithCI (sqlstate[sql_count].sql, "SAVEPOINT"))
	{
	  char *p = NULL;
	  p = sqlstate[sql_count].sql;
	  p = p + strlen ("savepoint ");
	  if (endswithsemicolon (p))
	    p[strlen (p) - 1] = 0;
	  res = cci_savepoint (conn, CCI_SP_SET, p, &error);
	  if (res >= 0)
	    {
	      fprintf (fp, "===================================================\n");
	      fprintf (fp, "0\n");
	    }
	  else
	    {
	      fprintf (stdout, "save point error: %s\n", error.err_msg);
	    }
	}
      else
	{
	  /* reset has_st for every SQL (execute + executebind) */
	  if (startswithCI (sqlstate[sql_count].sql, "show trace;"))
	    {
	      has_st = 1;
	    }
	  else
	    {
	      has_st = 0;
	    }

	  /*
	   * As cqt chooses (Sql.isPrep): a statement with a '?' outside quotes and a line of values runs
	   * through prepareStatement(); any other statement as it is, its line of values left unused.
	   */
	  if (parameter[sql_count] != NULL && is_prep (sqlstate[sql_count].sql))
	    {
	      executebind (fp, conn, parameter[sql_count], &sqlstate[sql_count]); 
	    }
	  else
	    {
	      execute (fp, conn, &sqlstate[sql_count]);
	    }
	}
    }

  //release
  if ((res = cci_disconnect (conn, &error)) < 0)
    {
      goto _END;
    }

  for (sql_count = 0; sql_count < total_sql; sql_count++)
    {
      if (sqlstate[sql_count].sql != NULL)
	free (sqlstate[sql_count].sql);
      if (parameter[sql_count] != NULL)
	free (parameter[sql_count]);
    }
  return 0;
_END:
  if (req > 0)
    cci_close_req_handle (req);
  if (conn > 0)
    res = cci_disconnect (conn, &error);
  for (sql_count = 0; sql_count < total_sql; sql_count++)
    {
      if (sqlstate[sql_count].sql != NULL)
	free (sqlstate[sql_count].sql);
      if (parameter[sql_count] != NULL)
	free (parameter[sql_count]);
    }
  return -1;
}

void
has_query_plan (char *casename)
{
  char *ret = NULL;

  if (casename == NULL)
    {
      queryplan = 0;
      exit (1);
    }

  int len = strlen (casename) + strlen (".queryPlan") - strlen (".sql") + 1;
  ret = (char *) malloc (len);
  memset (ret, 0, len);
  strncpy (ret, casename, strlen (casename) - strlen (".sql"));
  strcat (ret, ".queryPlan");
  if (access (ret, 0) != -1)
    {
      queryplan = 1;
    }
  free (ret);
}

int
cmp_result_files (char *a, char *b)
{
  FILE *fp1;
  FILE *fp2;
  int ch1, ch2;
  int ret = -1;

  fp1 = fopen (a, "r");
  fp2 = fopen (b, "r");

  if ((fp1 == NULL) || (fp2 == NULL))
    {
      printf ("Error in the file n");
    }
  else
    {
      /* as cqt compares them (ConsoleBO): without any CR or LF, so that only the text decides */
      do
	ch1 = getc (fp1);
      while (ch1 == '\r' || ch1 == '\n');
      do
	ch2 = getc (fp2);
      while (ch2 == '\r' || ch2 == '\n');
      while ((ch1 != EOF) && (ch2 != EOF) && (ch1 == ch2))
	{
	  do
	    ch1 = getc (fp1);
	  while (ch1 == '\r' || ch1 == '\n');
	  do
	    ch2 = getc (fp2);
	  while (ch2 == '\r' || ch2 == '\n');
	}

      if (ch1 == ch2)
	ret = 0;
      else if (ch1 != ch2)
	ret = 1;

      fclose (fp1);
      fclose (fp2);
    }
  return ret;
}

char *
getanswerfile (const char *casename)
{
  char *p1 = NULL;
  char *p2 = NULL;
  char *p = NULL;
  char *answer_str = NULL;
  char *ext_answer_str = NULL;
  int len_p1, len_p2, len;

  if (casename == NULL)
    return NULL;

  p1 = strstr (casename, "/cases/");
  p2 = p1 + strlen ("/cases/");
  len_p1 = p1 - casename;
  len_p2 = strlen (p2) - strlen ("sql");
  len = sizeof (char) * (len_p1 + len_p2 + strlen ("/answers/") + strlen ("answer") + 1);

  p = malloc (len);
  answer_str = p;

  memset (p, 0, len);
  p = strncpy (p, casename, len_p1);
  p += len_p1;
  p = strncpy (p, "/answers/", strlen ("/answers/"));
  p += strlen ("/answers/");
  p = strncpy (p, p2, len_p2);
  p += len_p2;
  p = strncpy (p, "answer", strlen ("answer"));

  ext_answer_str = malloc (strlen (answer_str) + strlen ("_cci") + 1);
  strcpy (ext_answer_str, answer_str);
  strcat (ext_answer_str, "_cci");
  if ((access (ext_answer_str, 0)) != -1)
    {
      free (answer_str);
      return ext_answer_str;
    }
  else
    {
      free (ext_answer_str);
      return answer_str;
    }
}

char *
getRelativeCasePath (char *filename)
{
  if (filename == NULL)
    return filename;

  char *res = NULL;
  int len = 0;
  char *pos = NULL;

  if (strstr (filename, "/scenario/"))
    {
      len = strlen ("/scenario");
      res = strstr (filename, "/scenario/");
    }
  else if (strstr (filename, "/cubrid-testcases-private/"))
    {
      len = strlen ("/cubrid-testcases-private");
      res = strstr (filename, "/cubrid-testcases-private/");
    }
  else if (strstr (filename, "/cubrid-testcases/"))
    {
      len = strlen ("/cubrid-testcases");
      res = strstr (filename, "/cubrid-testcases/");
    }

  res = res + len + 1;

  return res;
}

char *
merge_result_path (const char *result_path, char *res_path)
{
  int len = 0;
  char *new_path = NULL;
  char *res_ralative_path = NULL;

  res_ralative_path = getRelativeCasePath (res_path);

  len = strlen (result_path) + strlen ("/") + strlen (res_ralative_path);
  new_path = malloc (sizeof (char) * (len + 1));
  sprintf (new_path, "%s/%s", result_path, res_ralative_path);
  return new_path;
}

long
getCurrentTime ()
{
  struct timeval curTime;
  gettimeofday (&curTime, NULL);
  return ((long) curTime.tv_sec) * 1000 + (long) curTime.tv_usec / 1000;
}

char *
getlogname (char *casename)
{
  char *res = NULL;
  if (casename == NULL)
    return NULL;

  int len = strlen (casename) + strlen ("result") - strlen ("sql") + 1;
  res = (char *) malloc (len);
  memset (res, 0, len);
  res = strncpy (res, casename, strlen (casename) - 4);
  res = strcat (res, ".result");

  return res;
}

int
main (int argc, char *argv[])
{
  int sql_count;
  int rs = -1;
  char *result;
  char *ans_file = NULL;
  char *test_type = NULL;
  char *urlproperty = NULL;
  long start_time, end_time, elapse_time;
  if (argc < 4)
    {
      printf ("At least 4 paremeters.\n");
      return -1;
    }

  port = atoi (argv[1]);
  dbname = argv[2];
  test_type = argv[3];
  char *filename = argv[4];
  result = argv[5];
  urlproperty = argv[6];

  //construct the url as "cci:CUBRID:localhost:33888:test_db:dba:12345:"
  snprintf (url, 256, "cci:CUBRID:%s:%d:%s:%s:%s:%s", host, port, dbname, user, passwd,
	    urlproperty == NULL ? "" : urlproperty);

  printf ("Case Name:%s\n", filename);

  //initialise the sqlstate, which is store the sql statements.
  for (sql_count = 0; sql_count < MAX_SQL_NUM; sql_count++)
    {
      sqlstate[sql_count].sql = NULL;
      sqlstate[sql_count].hasqp = 0;
      parameter[sql_count] = NULL;
    }

  //get the sql statements from sql file.
  readFile (filename);

  //judge if this sql file have a queryplan file.
  has_query_plan (filename);

  //get the answer file path.
  answername = getanswerfile (filename);

  //construct a result file at the same dir as sql file.
  resname = getlogname (filename);
  if (resname == NULL)
    {
      return -1;
    }

  //open the sql file which will be test.
  FILE *fp = NULL;
  fp = fopen (resname, "w+");

  //begin to test the case by cci.
  start_time = getCurrentTime ();
  int ret = test (fp);
  end_time = getCurrentTime ();
  elapse_time = end_time - start_time;
  //end to test the case by cci.

  if (fp)
    {
      fclose (fp);
    }

  //start result log file
  init_log (result);
  rs = cmp_result_files (resname, answername);
  //write the compare result into summary file.
  char *case_file = getRelativeCasePath (filename);
  if (rs == 0)
    {
      fprintf (result_recorder, "TestCase: %s", case_file);
      fprintf (result_recorder, "\t%s:%ld\n", ":OK", elapse_time);
      printf ("Test Result: OK\n");
    }
  else
    {
      fprintf (result_recorder, "TestCase: %s", case_file);
      fprintf (result_recorder, "\t%s:%ld\n", ":NOK", elapse_time);
      char *result_p = NULL;
      char *pos = NULL;

      //mkdir folder for result, and create result file for failed cases
      result_p = merge_result_path (result, resname);
      mkdir_r (result_p, result);
      copyfile (resname, result_p);
      if (result_p != NULL)
	free (result_p);

      char sqllist[255] = { 0 };
      strcpy (sqllist, result);
      strcat (sqllist, "/");
      strcat (sqllist, case_file);
      copyfile (filename, sqllist);

      //mkdir folder for answer, and create result file for failed cases
      result_p = merge_result_path (result, answername);
      printf ("----answer name----: %s\n", answername);
      mkdir_r (result_p, result);
      copyfile (answername, result_p);
      if (result_p != NULL)
	free (result_p);
      printf ("Test Result: NOK\n");
    }

  close_log ();
  if (resname != NULL)
    free (resname);
  if (answername != NULL)
    free (answername);
  if (summarylog != NULL)
    free (summarylog);
  return ret;
}
