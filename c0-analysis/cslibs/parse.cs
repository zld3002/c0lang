public class _l_parse
{
	public static P<bool> parse_bool (string s)
	{
		P<bool> result = null;
		if (s == "true")
			result = new P<bool>(true);
		if (s == "false")
			result = new P<bool>(false);
		return result;
	}

	public static P<int> parse_int (string s, int b)
	{
		P<int> result = null;
		try
		{
			if (s[0] == '+')
				return null;
			int ival = System.Convert.ToInt32(s, b);
			result = new P<int>(ival);
		}
		catch (System.Exception) {result = null;}
		return result;
	}
}
