
public class _l_string
{

	public static int string_length(string s)
	{
		return s.Length;
	}

	public static char string_charat(string s, int index)
	{
		return s[index];
	}

	public static string string_join(string a, string b)
	{
		return string.Concat(a, b);
	}

	public static string string_sub(string a, int start, int end)
	{
		return a.Substring(start, end - start);
	}

	public static bool string_equal(string a, string b)
	{
		return 0 == string_compare(a, b);
	}

	public static int string_compare(string a, string b)
	{
		return a.CompareTo(b);
	}

	public static string string_fromint(int i)
	{
		return ("" + i);
	}

	public static string string_frombool(bool b)
	{
		return ("" + b);
	}

	public static string string_fromchar(char c)
	{
		return ("" + c);
	}

	public static string string_tolower(string s)
	{
		return s.ToLower();
	}

	public static char[] string_to_chararray(string s)
	{
		char[] chars = s.ToCharArray();
		char[] with_null = new char[chars.Length+1];
		for (int i = 0; i < chars.Length; i++)
		{
			with_null[i] = chars[i];
		}
		with_null[chars.Length] = '\0';
		return with_null;
	}

	public static string string_from_chararray(char[] A)
	{
		if (A[A.Length-1] != '\0')
			throw new System.IndexOutOfRangeException();
		else
		{
			char[] no_null = new char[A.Length-1];
			for (int i = 0; i < no_null.Length; i++)
				no_null[i] = A[i];
			return new string(no_null);
		}
	}

	public static int char_ord (char c)
	{
		return (int) c;
	}

	public static char char_chr (int n)
	{
		if (0 > n || n > 127)
			C0Program.assert(false, "character outside ASCII range (0..127)");
		return (char)n;
	}

}
