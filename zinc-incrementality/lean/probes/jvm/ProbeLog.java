/** Rendered library methods call `ran` with their owner, so the probe sees which method ran. */
public final class ProbeLog {
  public static String last;

  public static void ran(String owner) { last = owner; }
}
