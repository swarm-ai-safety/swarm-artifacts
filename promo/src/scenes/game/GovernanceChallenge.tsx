import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

export const GovernanceChallenge: React.FC = () => {
  const frame = useCurrentFrame();

  // Title
  const titleP = spring({ frame, fps: 30, config: { damping: 200 } });

  // Slider animation: tax rate moves from 0% to 15% over frames 40-140
  const sliderProgress = interpolate(frame, [40, 140], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const taxRate = Math.round(sliderProgress * 15);

  // Welfare bar reacts: goes up then down showing the tradeoff
  // Peaks around 8% tax, drops after
  const welfareRaw =
    sliderProgress < 0.53
      ? interpolate(sliderProgress, [0, 0.53], [0.3, 0.85])
      : interpolate(sliderProgress, [0.53, 1], [0.85, 0.45]);
  const welfareP = Math.max(
    0,
    spring({ frame: frame - 30, fps: 30, config: { damping: 100 } }),
  );

  // Challenge text
  const challengeP = Math.max(
    0,
    spring({ frame: frame - 150, fps: 30, config: { damping: 200 } }),
  );

  // Subtitle
  const subP = Math.max(
    0,
    spring({ frame: frame - 15, fps: 30, config: { damping: 200 } }),
  );

  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(ellipse at 50% 50%, ${colors.accentDim}12, ${colors.bg} 70%)`,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        fontFamily: fonts.heading,
      }}
    >
      {/* Grid overlay */}
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

      {/* Title */}
      <div
        style={{
          fontSize: 44,
          fontWeight: 700,
          color: colors.text,
          opacity: titleP,
          textAlign: "center",
          lineHeight: 1.4,
          marginBottom: 20,
          zIndex: 1,
        }}
      >
        Set the tax rate.
        <br />
        Control the circuit breaker.
      </div>

      <div
        style={{
          fontSize: 28,
          color: colors.textDim,
          opacity: subP,
          marginBottom: 80,
          zIndex: 1,
        }}
      >
        Governance levers shape the ecosystem
      </div>

      {/* Tax rate slider */}
      <div
        style={{
          width: 800,
          zIndex: 1,
          opacity: welfareP,
        }}
      >
        {/* Label */}
        <div
          style={{
            display: "flex",
            justifyContent: "space-between",
            marginBottom: 16,
          }}
        >
          <span style={{ fontSize: 28, color: colors.textDim }}>Tax Rate</span>
          <span
            style={{
              fontSize: 36,
              fontFamily: fonts.mono,
              fontWeight: 700,
              color: colors.accent,
            }}
          >
            {taxRate}%
          </span>
        </div>

        {/* Slider track */}
        <div
          style={{
            width: "100%",
            height: 12,
            borderRadius: 6,
            background: `${colors.textMuted}40`,
            position: "relative",
            marginBottom: 60,
          }}
        >
          {/* Fill */}
          <div
            style={{
              width: `${sliderProgress * 100}%`,
              height: "100%",
              borderRadius: 6,
              background: `linear-gradient(90deg, ${colors.success}, ${colors.accent}, ${colors.warning})`,
            }}
          />
          {/* Thumb */}
          <div
            style={{
              position: "absolute",
              left: `${sliderProgress * 100}%`,
              top: "50%",
              transform: "translate(-50%, -50%)",
              width: 28,
              height: 28,
              borderRadius: "50%",
              background: colors.accent,
              boxShadow: `0 0 16px ${colors.accent}60`,
            }}
          />
        </div>

        {/* Welfare bar */}
        <div
          style={{
            display: "flex",
            justifyContent: "space-between",
            marginBottom: 16,
          }}
        >
          <span style={{ fontSize: 28, color: colors.textDim }}>
            Ecosystem Welfare
          </span>
          <span
            style={{
              fontSize: 36,
              fontFamily: fonts.mono,
              fontWeight: 700,
              color:
                welfareRaw > 0.7
                  ? colors.success
                  : welfareRaw > 0.5
                    ? colors.warning
                    : colors.danger,
            }}
          >
            {(welfareRaw * 100).toFixed(0)}%
          </span>
        </div>

        <div
          style={{
            width: "100%",
            height: 24,
            borderRadius: 12,
            background: `${colors.textMuted}40`,
            overflow: "hidden",
          }}
        >
          <div
            style={{
              width: `${welfareRaw * 100}%`,
              height: "100%",
              borderRadius: 12,
              background:
                welfareRaw > 0.7
                  ? colors.success
                  : welfareRaw > 0.5
                    ? `linear-gradient(90deg, ${colors.success}, ${colors.warning})`
                    : `linear-gradient(90deg, ${colors.warning}, ${colors.danger})`,
              transition: "background 0.1s",
            }}
          />
        </div>
      </div>

      {/* Challenge text */}
      <div
        style={{
          fontSize: 32,
          color: colors.warning,
          fontStyle: "italic",
          opacity: challengeP,
          transform: `translateY(${interpolate(challengeP, [0, 1], [20, 0])}px)`,
          marginTop: 80,
          textAlign: "center",
          lineHeight: 1.5,
          zIndex: 1,
        }}
      >
        Find the balance before
        <br />
        the ecosystem collapses
      </div>
    </AbsoluteFill>
  );
};
