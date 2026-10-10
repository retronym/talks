/**
 * Rendered library methods call `ran` with their owner, so the probe sees which method ran; a put
 * site leaves its receiver in `obj`.
 */
public final class ProbeLog {
  public static String last;
  public static Object obj;

  public static void ran(String owner) { last = owner; }
}
