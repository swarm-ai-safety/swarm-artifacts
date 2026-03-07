import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

export const Welcome: React.FC = () => {
  const frame = useCurrentFrame();

  const gradientX = interpolate(frame, [0, 180], [30, 70]);
  const gradientY = interpolate(frame, [0, 180], [30, 60]);

  const titleProgress = spring({ frame, fps: 30, config: { damping: 200 } });
  const titleScale = interpolate(titleProgress, [0, 1], [0.8, 1]);

  const lineWidth = interpolate(
    spring({ frame: frame - 15, fps: 30, config: { damping: 100 } }),
    [0, 1],
    [0, 500],
  );

  const subtitleProgress = spring({
    frame: frame - 25,
    fps: 30,
    config: { damping: 200 },
  });
  const sub = Math.max(0, subtitleProgress);

  const tagProgress = spring({
    frame: frame - 50,
    fps: 30,
    config: { damping: 200 },
  });
  const tag = Math.max(0, tagProgress);

  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(ellipse at ${gradientX}% ${gradientY}%, ${colors.accentDim}15, ${colors.bg} 70%)`,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        fontFamily: fonts.heading,
      }}
    >
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundImage: `
            linear-gradient(${colors.gridLine} 1px, transparent 1px),
            linear-gradient(90deg, ${colors.gridLine} 1px, transparent 1px)
          `,
          backgroundSize: "80px 80px",
          opacity: 0.3,
        }}
      />

      <div
        style={{
          fontSize: 48,
          fontWeight: 600,
          color: colors.textDim,
          opacity: titleProgress,
          letterSpacing: "0.12em",
          marginBottom: 12,
        }}
      >
        Contributing to
      </div>

      <div
        style={{
          fontSize: 130,
          fontWeight: 800,
          color: colors.text,
          letterSpacing: "0.15em",
          opacity: titleProgress,
          transform: `scale(${titleScale})`,
        }}
      >
        SWARM
      </div>

      <div
        style={{
          width: lineWidth,
          height: 2,
          background: `linear-gradient(90deg, transparent, ${colors.accent}, transparent)`,
          marginTop: 16,
          marginBottom: 24,
        }}
      />

      <div
        style={{
          fontSize: 36,
          fontWeight: 600,
          color: colors.accent,
          opacity: sub,
          transform: `translateY(${interpolate(sub, [0, 1], [20, 0])}px)`,
          letterSpacing: "0.06em",
        }}
      >
        A Beginner's Guide to Open Source
      </div>

      <div
        style={{
          fontSize: 24,
          color: colors.textDim,
          opacity: tag,
          transform: `translateY(${interpolate(tag, [0, 1], [20, 0])}px)`,
          marginTop: 28,
          maxWidth: 700,
          textAlign: "center",
          lineHeight: 1.5,
          fontStyle: "italic",
        }}
      >
        No experience required. Just curiosity and a terminal.
      </div>
    </AbsoluteFill>
  );
};
